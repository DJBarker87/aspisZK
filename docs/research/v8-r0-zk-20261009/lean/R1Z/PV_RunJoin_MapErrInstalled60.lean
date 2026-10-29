import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.ProverRwOuterMapErr
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MapErrInstalled60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
variable [ExternalTypes]

def install (ops : ExternalFuns) : ExternalFuns := {ops with op12:=@ProverRwOuterMapErr.map_err}

theorem source (ops : ExternalFuns) {T E F O : Type} (f : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) :
    @core.result.Result.map_err _ (install ops) T E F O f status closure=
      ProverRwRngNativeBody.core.result.Result.map_err f status closure :=
  ProverRwOuterMapErr.source f status closure

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem installed (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op12 (types base) (selected base heap box (install ops))=@ProverRwOuterMapErr.map_err := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_12]
  rfl

#print axioms source
#print axioms installed
end R1Z.PV_RunJoin_MapErrInstalled60
