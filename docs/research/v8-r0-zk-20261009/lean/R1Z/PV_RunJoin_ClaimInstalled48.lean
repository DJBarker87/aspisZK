import R1Z.PV_RunJoin_ClaimStart48
import R1Z.PV_RunJoin_ClaimImage48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point)
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Slice Column) (point : Point)
    (small : columns.length≤14336) :
    mapResult (fun out => out.val)
      (@prover.opening_claim_bytes (types base) (selected base heap box ops) columns point)=
      mapResult PV_RunJoin_ClaimImage48.bytes
        (PV_RunJoin_ClaimImage48.values
          (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val) := by
  rw [@PV_RunJoin_ClaimStart48.complete (types base) (selected base heap box ops) columns point small,
    PV_RunJoin_ClaimProducer48.complete base heap box ops columns.val point]
  have room : (alloc.vec.Vec.new U8).length+32*columns.val.length≤Usize.max := by
    have len : columns.val.length=columns.length := rfl
    change 0+32*columns.val.length≤Usize.max
    rw [len]
    scalar_tac
  rw [PV_RunJoin_ClaimImage48.complete _ columns.val _ room]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_ClaimInstalled48
