import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_DropGate
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- Concrete glue is supplied by its type's source/MIR law; not by a universal Drop. -/
structure Command (m : Memory) where
 token : Token
 cell : Cell
 owner : Nat
 owned : Owned m owner token cell
 unborrowed : NoLoans m token

def execute {S X E : Type} (w : State S X) (c : Command w.memory)
 (glue : Token → Action S X E Unit) := dropOwned c.owner glue w

theorem preworld {S X E : Type} (w : State S X) (c : Command w.memory)
 (glue : Token → Action S X E Unit) :
 execute w c glue=glue c.token {w with memory := take c.owner w.memory} := by
 simp [execute,dropOwned,c.owned.2.1]

/-- A shared or exclusive loan blocks construction of a consuming command. -/
theorem loan_blocks (m : Memory) (l : Loan) :
 ¬∃ c : Command (borrow l m), c.token=l.token := by
 intro ⟨c,h⟩
 have ne:=c.unborrowed l List.mem_cons_self
 exact ne h.symm
#print axioms preworld
#print axioms loan_blocks
end R1Z.PV_OWN_DropGate
