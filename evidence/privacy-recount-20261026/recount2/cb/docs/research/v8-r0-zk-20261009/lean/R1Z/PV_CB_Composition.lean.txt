import R1Z.PV_CB_Heap
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Composition
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Compose the installed value/source callbacks; each unassigned field remains
in the input dictionary. This supplies no RunJoin or native world instance. -/
@[reducible] def selected := @PV_CB_Heap.selected

theorem take (ops : ExternalFuns) {T : Type} (d : core.default.Default T) (x : T) :
    (selected ops).op3 d x = ProverRwSuccessGeneric.take d x := rfl
theorem pop (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op33 A v = ProverRwSuccessVectors.pop A v := rfl
theorem empty (ops : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (selected ops).op34 A v = ProverRwSuccessVectors.isEmpty A v := rfl
theorem default_vec (ops : ExternalFuns) (T : Type) :
    (selected ops).op35 T = .ok (alloc.vec.Vec.new T) := rfl
theorem array (ops : ExternalFuns) {T : Type} (A : Type) (N : Usize) (v : alloc.vec.Vec T) :
    (selected ops).op36 A N v = ProverRwSuccessVectors.toArray A N v := rfl
#print axioms take
#print axioms pop
#print axioms empty
#print axioms default_vec
#print axioms array
end R1Z.PV_CB_Composition
