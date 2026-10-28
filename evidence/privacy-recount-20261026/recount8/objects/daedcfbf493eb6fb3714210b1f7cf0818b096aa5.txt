import R1Z.ProverRwSuccessPhiSource
import R1Z.ProverCommitArray49
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessGeneric
open Aeneas Aeneas.Std Result ProverRwFull

def take {T : Type} (inst : core.default.Default T) (x : T) : Result (T × T) := do
  let replacement ← inst.default
  .ok (x,replacement)
def pointClone {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) : Result (aspis_core.r0.domain.Point E) := do
  let x ← inst.clone p.x
  let y ← inst.clone p.y
  .ok ⟨x,y⟩

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessHashes.selected ops with
    op3 := take, op77 := pointClone,
    op80 := ProverRwSuccessPhiSource.generic54.phi_inverse}

theorem take_order (ops : ExternalFuns) {T : Type} (inst : core.default.Default T) (x : T) :
    (selected ops).op3 inst x = (do let replacement ← inst.default; .ok (x,replacement)) := rfl

theorem point_clone (ops : ExternalFuns) {E : Type} (inst : core.clone.Clone E)
    (p : aspis_core.r0.domain.Point E) :
    (selected ops).op77 inst p = (do
      let x ← inst.clone p.x
      let y ← inst.clone p.y
      .ok ⟨x,y⟩) := rfl

theorem phi_source (ops : ExternalFuns) {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (x y : E) (h : Array E 4#usize) :
    (selected ops).op80 inst x y h = ProverRwSuccessPhiSource.generic54.phi_inverse inst x y h := rfl
#print axioms take_order
#print axioms point_clone
#print axioms phi_source
end R1Z.ProverRwSuccessGeneric
