import R1Z.PV_RunJoin_ClaimProducerCell48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimProducer48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point W)
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

def run (evaluate : Column → Result W) : List Column → alloc.vec.Vec U8 → Result (alloc.vec.Vec U8)
  | [],out => ok out
  | column::tail,out => do
    let value ← evaluate column
    let next ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
      (Array.to_slice (PV_RunJoin_FlatBytes35.wire value))
    run evaluate tail next

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : List Column) (point : Point)
    (out : alloc.vec.Vec U8) :
    @PV_RunJoin_ClaimList48.run (types base) (selected base heap box ops) point columns out=
      run (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns out := by
  induction columns generalizing out with
  | nil => rfl
  | cons column tail ih =>
    simp only [PV_RunJoin_ClaimList48.run]
    rw [PV_RunJoin_ClaimProducerCell48.complete base heap box ops point column out]
    simp only [run,bind_assoc,ih]

#print axioms complete
end R1Z.PV_RunJoin_ClaimProducer48
