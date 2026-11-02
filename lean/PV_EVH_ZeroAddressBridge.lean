import PV_EVH_DeployedZeroWorld
set_option autoImplicit false
namespace PV_EVH_ZeroAddressBridge
open PV_EVH_HeapOwnership
open PV_EVH_ZeroizeArray (events cells)

/-- Resolve the retained owner's offsets to physical byte addresses. The key
is not inferred from equal byte contents. Exclusive-region validity is separate. -/
def physical (base : Nat) : PV_EVH_ZeroizeArray.Event → PV_EVH_DeployedZeroWorld.Event
  | .store _ offset => .volatileWrite (base+offset) 0
  | .barrier _ offset => .asmReadBarrier (base+offset)

theorem physical_trace (key : Key) (base offset n : Nat) :
    (events key offset n).map (physical base) =
      PV_EVH_DeployedZeroTrace.trace (base+offset) n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [events,List.map_cons,physical,PV_EVH_DeployedZeroTrace.trace,
      List.cons_append,List.nil_append,ih,Nat.add_assoc]

/-- Connect the local byte recursion to the recorded deployed world law.
Both the zero output and the physical write/barrier history are retained. -/
theorem cells_deployed (key : Key) (base offset : Nat) (values : PV_RJ4IDB.Bytes) :
    (cells key offset values).1 = List.replicate values.length 0 ∧
    (cells key offset values).2.map (physical base) =
      PV_EVH_DeployedZeroTrace.trace (base+offset) values.length := by
  rw [PV_EVH_ZeroizeArray.cells_exact]
  exact ⟨rfl,physical_trace key base offset values.length⟩

theorem cursor_history {F : Type} (key : Key) (base n : Nat)
    (w : PV_EVH_DeployedZeroWorld.World F) :
    (PV_EVH_DeployedZeroCursor.run (base+n) n base w).history =
      w.history ++ (events key 0 n).map (physical base) := by
  rw [PV_EVH_DeployedZeroCursor.source,PV_EVH_DeployedZeroTrace.history,physical_trace]
  rfl

/-- This is an L3 memory fact. It says nothing about register/spill copies,
silence, allocator erasure, or witness independence of the observer. -/
theorem cursor_overwrites {F : Type} (base n i : Nat)
    (w : PV_EVH_DeployedZeroWorld.World F) (hi : i<n) :
    (PV_EVH_DeployedZeroCursor.run (base+n) n base w).memory (base+i) = 0 := by
  rw [PV_EVH_DeployedZeroCursor.source]
  exact PV_EVH_DeployedZeroWorld.overwritten base n w i hi

#print axioms physical_trace
#print axioms cells_deployed
#print axioms cursor_history
#print axioms cursor_overwrites
end PV_EVH_ZeroAddressBridge
