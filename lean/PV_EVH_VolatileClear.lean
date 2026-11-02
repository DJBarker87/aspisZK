import PV_EVH_HeapOwnership
set_option autoImplicit false
namespace PV_EVH_VolatileClear
open PV_EVH_Runtime PV_EVH_HeapOwnership
open PV_RJ4IDB (Bytes NativeEvent)

inductive Event where
  | store (key : Key) (offset : Nat)
  | fence
  deriving DecidableEq

/-- Each recursive step is one volatile cell write; no uninitialized capacity
is read or cleared by the shipped volatile_clear slice loop. -/
def cells (key : Key) (offset : Nat) : Bytes → Bytes × List Event
  | [] => ([],[])
  | _ :: tail =>
    let rest := cells key (offset+1) tail
    (0 :: rest.1, Event.store key offset :: rest.2)

def stores (key : Key) (offset : Nat) : Nat → List Event
  | 0 => []
  | n+1 => Event.store key offset :: stores key (offset+1) n

def clear (key : Key) (values : Bytes) : Bytes × List Event :=
  let out := cells key 0 values
  (out.1,out.2 ++ [.fence])

theorem cells_exact (key : Key) (values : Bytes) (offset : Nat) :
    cells key offset values = (List.replicate values.length 0,stores key offset values.length) := by
  induction values generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    simp only [cells, ih, List.length_cons, List.replicate_succ, stores]

theorem clear_exact (key : Key) (values : Bytes) :
    clear key values =
      (List.replicate values.length 0, stores key 0 values.length ++ [.fence]) := by
  simp only [clear,cells_exact]

/-- Spare backing remains untouched. This is a write model, not a proof that
native volatile writes or their addresses are correctly associated. -/
def clearBlock (b : Block) (initialized : Nat) : Block :=
  {b with bytes := List.replicate initialized 0 ++ b.bytes.drop initialized}

theorem clear_keeps_identity (b : Block) (n : Nat) :
    (clearBlock b n).identity = b.identity ∧
    (clearBlock b n).owner = b.owner ∧
    (clearBlock b n).address = b.address ∧
    (clearBlock b n).layout = b.layout := ⟨rfl,rfl,rfl,rfl⟩

theorem clear_length (b : Block) (n : Nat) (h : n ≤ b.bytes.length) :
    (clearBlock b n).bytes.length = b.bytes.length := by
  simp only [clearBlock,List.length_append,List.length_replicate,List.length_drop]
  exact Nat.add_sub_of_le h

theorem clear_initialized (b : Block) (n : Nat) :
    (clearBlock b n).bytes.take n = List.replicate n 0 := by
  simp only [clearBlock]
  simpa only [List.length_replicate] using
    (show ((List.replicate n (0 : UInt8)) ++ b.bytes.drop n).take
      (List.replicate n (0 : UInt8)).length = List.replicate n 0 from List.take_left)

#print axioms cells_exact
#print axioms clear_exact
#print axioms clear_keeps_identity
#print axioms clear_length
#print axioms clear_initialized
end PV_EVH_VolatileClear
