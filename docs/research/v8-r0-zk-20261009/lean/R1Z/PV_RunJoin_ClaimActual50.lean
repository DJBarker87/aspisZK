import R1Z.PV_RunJoin_ClaimEvaluationActual50
import R1Z.PV_RunJoin_ClaimProducerCongruence50
import R1Z.PV_RunJoin_ClaimStart48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimActual50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_ClaimThread48 (Column Point W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

def run (columns : Slice Column) (point : Point) : Result (alloc.vec.Vec U8) :=
  PV_RunJoin_ClaimProducer48.run (PV_RunJoin_ClaimEvaluationActual50.run point) columns.val (alloc.vec.Vec.new U8)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (columns : Slice Column) (point : Point) (small : columns.length≤14336) :
    @prover.opening_claim_bytes (types base)
      (selected base heap box (@PV_DL_EncoderSelected.selected (types base) ops)) columns point=run columns point := by
  rw [@PV_RunJoin_ClaimStart48.complete (types base)
    (selected base heap box (@PV_DL_EncoderSelected.selected (types base) ops)) columns point small]
  rw [PV_RunJoin_ClaimProducer48.complete]
  exact PV_RunJoin_ClaimProducerCongruence50.complete _ _
    (PV_RunJoin_ClaimEvaluationActual50.complete base heap box ops point) _ _
#print axioms run
#print axioms complete
end R1Z.PV_RunJoin_ClaimActual50
