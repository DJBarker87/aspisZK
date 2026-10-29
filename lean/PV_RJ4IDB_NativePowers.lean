import PV_RJ4IDB_FieldWide
import PV_RJ4IDB_Op254
import R1Z.ProverRwP6PowersNativeCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_NativePowers
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
/-- Explicit deployed primitive interpretation. Only op47 differs in syntax;
the complete Result transport proves its source meaning equals the retained
captured primitive, rather than assuming this installation equality. -/
def primitives (ops : ExternalFuns) : ExternalFuns :=
 {ProverRwP6BoundaryInstall.selected ops with op47 := PV_RJ4IDB_FieldWide.mul}

theorem primitives_equal (ops : ExternalFuns) :
 primitives ops = ProverRwP6BoundaryInstall.selected ops := by
 have h : PV_RJ4IDB_FieldWide.mul = wMul := by funext a b; exact PV_RJ4IDB_FieldWide.complete a b
 unfold primitives
 rw [h]
 rfl

def callback (ops : ExternalFuns) (N : Usize) (x : W) : Result (Array W N) :=
 @PV_RJ4IDB_PowersControl.powers _ (primitives ops) N x

theorem deployed_callback (ops : ExternalFuns) (N : Usize) (x : W) :
 callback ops N x = ProverRwP6PowersInstall.powers ops N x := by
 unfold callback
 rw [primitives_equal]
 exact PV_RJ4IDB_Op254.entry ops N x

def installed (ops : ExternalFuns) : ExternalFuns := {ops with op254 := callback ops}

theorem deployed_installation (ops : ExternalFuns) :
 installed ops = {ops with op254 := ProverRwP6PowersInstall.powers ops} := by
 have h : callback ops = ProverRwP6PowersInstall.powers ops := by
  funext N x
  exact deployed_callback ops N x
 unfold installed
 rw [h]
#print axioms primitives_equal
#print axioms deployed_callback
#print axioms deployed_installation
end R1Z.PV_RJ4IDB_NativePowers
