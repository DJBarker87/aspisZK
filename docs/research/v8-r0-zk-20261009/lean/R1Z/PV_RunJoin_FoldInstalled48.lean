import R1Z.PV_RunJoin_FoldCongruence48
import R1Z.PV_RunJoin_RoundInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_FoldThread44 (W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Slice W) (alpha : W) (dual : Bool) (small : q.length/4≤256) :
    @prover.fold (types base) (selected base heap box ops) q alpha dual=
      @prover.fold (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) q alpha dual := by
  exact @PV_RunJoin_FoldCongruence48.complete (types base)
    (selected base heap box ops) (@ProverRwP6BodyCandidate.selected (types base) ops)
    (PV_RunJoin_BatchFields48.mul base heap box ops)
    (PV_RunJoin_BatchFields48.add base heap box ops)
    (PV_RunJoin_RoundInstalled48.scale base heap box ops) q alpha dual small
#print axioms complete
end R1Z.PV_RunJoin_FoldInstalled48
