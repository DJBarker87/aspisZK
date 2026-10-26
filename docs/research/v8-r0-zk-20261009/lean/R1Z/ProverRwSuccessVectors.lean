import R1Z.ProverRwSuccessWireInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessVectors
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
-- These are logical value operations on the existing Aeneas Vec carrier.
-- Allocation failure, allocator/ABI and destruction association remain open.
def pop {T : Type} (_A : Type) (v : alloc.vec.Vec T) :
    Result (Option T × alloc.vec.Vec T) :=
  .ok (v.val.getLast?,⟨v.val.dropLast,by
    rw [List.length_dropLast]
    exact Nat.le_trans (Nat.sub_le _ _) v.property⟩)
def isEmpty {T : Type} (_A : Type) (v : alloc.vec.Vec T) : Result Bool :=
  .ok (decide (v.val=[]))
def empty (T : Type) : Result (alloc.vec.Vec T) := .ok (Aeneas.Std.alloc.vec.Vec.new T)
def toArray {T : Type} (_A : Type) (N : Usize) (v : alloc.vec.Vec T) :
    Result (core.result.Result (Array T N) (alloc.vec.Vec T)) :=
  if h : v.val.length=N.val then .ok (.Ok ⟨v.val,h⟩) else .ok (.Err v)
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessWireInstall.selected ops with
    op33 := pop,op34 := isEmpty,
    op35 := empty,op36 := toArray}

theorem pop_payload (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    ∃ tail, (selected ops).op33 A v=.ok (v.val.getLast?,tail) ∧ tail.val=v.val.dropLast :=
  ⟨_,rfl,rfl⟩
theorem empty_test (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op34 A v=.ok true ↔ v.val=[] := by
  change (.ok (decide (v.val=[])) : Result Bool)=.ok true ↔ _
  simp

theorem empty_value (ops : ExternalFuns) (T : Type) :
    ∃ v, (selected ops).op35 T=.ok v ∧ v.val=[] := ⟨_,rfl,rfl⟩
theorem array_accept (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize)
    (v : alloc.vec.Vec T) (length : v.val.length=N.val) :
    (selected ops).op36 A N v=.ok (.Ok ⟨v.val,length⟩) := by
  change toArray A N v=_
  simp only [toArray,length,dif_pos]
theorem array_reject (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize)
    (v : alloc.vec.Vec T) (length : v.val.length≠N.val) :
    (selected ops).op36 A N v=.ok (.Err v) := by
  change toArray A N v=_
  simp only [toArray,dif_neg length]
#print axioms pop_payload
#print axioms empty_test
#print axioms empty_value
#print axioms array_accept
#print axioms array_reject
end R1Z.ProverRwSuccessVectors
