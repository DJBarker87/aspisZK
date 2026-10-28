import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_CoefficientInstalled45
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightCoefficient46
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) {T : Type} (copy : core.marker.Copy T) (p : Nat → T) :
    @transport.Variant.coefficients (types base) (selected base heap box ops) T copy .S2
      (ProverCommitArray49.array 1024#usize p)=
      .ok (ProverCommitArray49.array 1024#usize (fun j => p (AspisR1.rowNat j))) := by
  change @ExternalFuns.op255 (types base) (selected base heap box ops) T copy .S2 _=_
  unfold selected
  rw [PV_B2_F_RawNative.preserved_255]
  exact @PV_RunJoin_CoefficientInstalled45.complete (types base) ops T copy p
#print axioms complete
end R1Z.PV_RunJoin_WeightCoefficient46
