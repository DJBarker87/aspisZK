import R1Z.PV_CB_Composition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Independent
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- These input dictionary fields no longer influence their selected callbacks. -/
theorem take (ops other : ExternalFuns) {T : Type} (d : core.default.Default T) (x : T) :
    (PV_CB_Composition.selected {ops with op3 := other.op3}).op3 d x =
      (PV_CB_Composition.selected ops).op3 d x := rfl
theorem pop (ops other : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (PV_CB_Composition.selected {ops with op33 := other.op33}).op33 A v =
      (PV_CB_Composition.selected ops).op33 A v := rfl
theorem empty (ops other : ExternalFuns) {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    (PV_CB_Composition.selected {ops with op34 := other.op34}).op34 A v =
      (PV_CB_Composition.selected ops).op34 A v := rfl
theorem default_vec (ops other : ExternalFuns) (T : Type) :
    (PV_CB_Composition.selected {ops with op35 := other.op35}).op35 T =
      (PV_CB_Composition.selected ops).op35 T := rfl
theorem array (ops other : ExternalFuns) {T : Type} (A : Type) (N : Usize) (v : alloc.vec.Vec T) :
    (PV_CB_Composition.selected {ops with op36 := other.op36}).op36 A N v =
      (PV_CB_Composition.selected ops).op36 A N v := rfl
#print axioms take
#print axioms pop
#print axioms empty
#print axioms default_vec
#print axioms array
end R1Z.PV_CB_Independent
