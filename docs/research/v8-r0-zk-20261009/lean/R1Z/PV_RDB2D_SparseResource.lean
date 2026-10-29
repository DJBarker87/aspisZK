import R1Z.PV_RDB2D_SparsePush
import R1Z.PV_RDB2D_SparseFree
namespace R1Z.PV_RDB2D_SparseResource
open Aeneas Aeneas.Std Result PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape
open PV_RDB2D_SparseFold
set_option autoImplicit false

abbrev Outcome (K S F : Type) := Option K × State S F
abbrev Handler (K S F : Type) := Action → State S F → Result (Outcome K S F)

def runWith {K S F : Type} (fold : List K → List (Entry K) → K → Result K)
    (ops : Ops K) (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler K S F) (isBoolean : K → Bool) (point column : List K)
    (build : List K → Result (List (Entry K))) (state : State S F) : Result (Outcome K S F) := do
  if column.length ≠ 1024 then ok (none,state) else
    let n := capacity isBoolean point
    let (out,after) ← issue allocate PV_RDB2D_SparseLayout.shape (PV_RDB2D_SparseLayout.empty K) n state
    match out.returned with
    | .error _ => handler (.abort (24*n) 8) {after with trace := after.trace++[.abort (24*n) 8]}
    | .ok () => do
      let entries ← build point
      let value ← fold column entries ops.zero
      let after ← PV_RDB2D_SparseFree.release deallocate out.buffer.address n after
      ok (some value,after)

def source {K S F : Type} (ops : Ops K) := @runWith K S F (PV_RDB2D_SparseFold.source ops) ops
def reference {K S F : Type} (ops : Ops K) := @runWith K S F (PV_RDB2D_SparseFold.reference ops) ops

/-- Complete resource-wrapper model, for every column and every primitive
Result. Concrete point scanning, weight construction, initialized byte memory
and raw QM31 method association are not asserted by this theorem. -/
theorem arbitrary_column_world {K S F : Type} (ops : Ops K) (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler K S F)
    (isBoolean : K → Bool) (point column : List K) (build : List K → Result (List (Entry K)))
    (state : State S F) :
    source ops allocate deallocate handler isBoolean point column build state=
      reference ops allocate deallocate handler isBoolean point column build state := by
  have hf : PV_RDB2D_SparseFold.source ops=PV_RDB2D_SparseFold.reference ops := by
    funext col entries acc
    exact arbitrary_column ops col entries acc
  unfold source reference
  rw [hf]

theorem wrong_length {K S F : Type} (ops : Ops K) (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler K S F)
    (isBoolean : K → Bool) (point column : List K) (build : List K → Result (List (Entry K)))
    (state : State S F) (h : column.length ≠ 1024) :
    source ops allocate deallocate handler isBoolean point column build state=ok (none,state) := by
  unfold source runWith
  exact if_pos h

#print axioms arbitrary_column_world
#print axioms wrong_length
end R1Z.PV_RDB2D_SparseResource
