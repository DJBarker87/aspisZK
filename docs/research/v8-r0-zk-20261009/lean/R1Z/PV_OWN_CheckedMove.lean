import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_CheckedMove
open PV_OWN_Heap PV_OWN_Operations
structure Command (m : Memory) where
 token : Token
 cell : Cell
 source : Nat
 destination : Nat
 owned : Owned m source token cell
 unborrowed : NoLoans m token
 empty : m.slots destination=none
 distinct : destination≠source

def execute {m : Memory} (c : Command m) : Memory :=
 move c.source c.destination c.token c.cell m

theorem transferred {m : Memory} (c : Command m) :
 Owned (execute c) c.destination c.token {c.cell with owner := c.destination} := by
 refine ⟨⟨put_same _ _ _,c.owned.1.2.1,c.owned.1.2.2⟩,?_,rfl⟩
 simp [execute,move,c.distinct]

theorem source_consumed {m : Memory} (c : Command m) : (execute c).slots c.source=none := by
 simp [execute,move]
#print axioms transferred
#print axioms source_consumed
end R1Z.PV_OWN_CheckedMove
