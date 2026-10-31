import R1Z.PV_RDCD4_LazyAccumulate
import R1Z.PV_RDCD4_LazyReconstruct
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyProducts
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell
def zero : Sums := [[0#u64,0#u64,0#u64],[0#u64,0#u64,0#u64],[0#u64,0#u64,0#u64]]
def step (left right : Array Q 3#usize) (sums : Sums) (index : Nat) : Result Sums := do
  let l ← read left.val index
  let r ← read right.val index
  PV_RDCD4_LazyAccumulate.source sums l r

def referenceStep (left right : Array Q 3#usize) (sums : Sums) (index : Nat) : Result Sums := do
  let l ← read left.val index
  let r ← read right.val index
  PV_RDCD4_LazyAccumulate.reference sums l r

theorem step_binding (left right : Array Q 3#usize) (sums : Sums) (index : Nat) :
    step left right sums index=referenceStep left right sums index := by
  simp only [step,referenceStep,PV_RDCD4_LazyAccumulate.binding]

def source (left right : Array Q 3#usize) : Result Q := do
  let sums ← PV_RDCD3_RangeLoop.source (step left right) ⟨0,3⟩ zero
  PV_RDCD4_LazyReconstruct.source sums

def reference (left right : Array Q 3#usize) : Result Q := do
  let s ← referenceStep left right zero 0
  let s ← referenceStep left right s 1
  let s ← referenceStep left right s 2
  PV_RDCD4_LazyReconstruct.source s

theorem binding (left right : Array Q 3#usize) : source left right=reference left right := by
  unfold source reference
  rw [PV_RDCD3_RangeLoop.complete _ 3 0 3 zero (by omega)]
  simp only [PV_RDCD3_RangeFold.ordered,step_binding,bind_assoc_eq,bind_tc_ok,
    PV_RDCD4_LazyChannels.bind_return]
#print axioms step_binding
#print axioms binding
end R1Z.PV_RDCD4_LazyProducts
