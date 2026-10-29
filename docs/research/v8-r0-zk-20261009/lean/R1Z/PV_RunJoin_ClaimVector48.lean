import R1Z.PV_RunJoin_ClaimProducer48
import R1Z.PV_RunJoin_ClaimStart48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimVector48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_ClaimThread48 (Column Point)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Slice Column) (point : Point)
    (small : columns.length≤14336) :
    @prover.opening_claim_bytes (types base) (selected base heap box ops) columns point=
      PV_RunJoin_ClaimProducer48.run
        (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val
        (alloc.vec.Vec.new U8) := by
  rw [@PV_RunJoin_ClaimStart48.complete (types base) (selected base heap box ops) columns point small]
  exact PV_RunJoin_ClaimProducer48.complete base heap box ops columns.val point _
#print axioms complete
end R1Z.PV_RunJoin_ClaimVector48
