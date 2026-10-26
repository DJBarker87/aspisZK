import R1Z.PV_CB_Composition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_VectorLaws
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem pop_length (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    ∃ tail, (PV_CB_Composition.selected ops).op33 A v = .ok (v.val.getLast?,tail) ∧
      tail.val.length = v.val.length - 1 := by
  refine ⟨_,rfl,?_⟩
  exact List.length_dropLast
theorem pop_none (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (∃ tail, (PV_CB_Composition.selected ops).op33 A v = .ok (none,tail)) ↔ v.val=[] := by
  change (∃ tail, (.ok (v.val.getLast?, _) : Result (Option T × alloc.vec.Vec T)) = .ok (none,tail)) ↔ _
  simp
theorem nonempty (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (PV_CB_Composition.selected ops).op34 A v = .ok false ↔ v.val ≠ [] := by
  change (.ok (decide (v.val=[])) : Result Bool) = .ok false ↔ _
  simp
theorem default_empty (ops : ExternalFuns) (T A : Type) :
    (do let v ← (PV_CB_Composition.selected ops).op35 T
        (PV_CB_Composition.selected ops).op34 A v) = .ok true := by rfl
#print axioms pop_length
#print axioms pop_none
#print axioms nonempty
#print axioms default_empty
end R1Z.PV_CB_VectorLaws
