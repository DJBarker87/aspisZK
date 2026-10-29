import R1Z.PV_RunJoin_RoundCongruence48
import R1Z.PV_RunJoin_BatchFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_RoundCellThread44 (W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem scale (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op52 (types base) (selected base heap box ops)=
      (@ProverRwP6BodyCandidate.selected (types base) ops).op52 := by
  unfold selected
  exact PV_B2_F_RawNative.preserved_52 base heap box _

attribute [local irreducible] selected PV_B2_F_RawNative.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q w : Slice W) (small : q.length/4≤256) :
    @prover.round (types base) (selected base heap box ops) q w=
      @prover.round (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) q w := by
  apply @PV_RunJoin_RoundCongruence48.complete (types base)
    (selected base heap box ops) (@ProverRwP6BodyCandidate.selected (types base) ops)
    (PV_RunJoin_BatchFields48.zero base heap box ops)
    (PV_RunJoin_BatchFields48.mul base heap box ops)
    (PV_RunJoin_BatchFields48.add base heap box ops) (scale base heap box ops) q w small
#print axioms scale
#print axioms complete
end R1Z.PV_RunJoin_RoundInstalled48
