import R1Z.PV_RunJoin_ClaimList48
import R1Z.PV_RunJoin_ClaimFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimProducerCell48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point W)
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

def evaluate (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (point : Point) (column : Column) : Result W :=
  @ExternalFuns.op79 (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) _
    (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
      (types base) (selected base heap box ops)) column point

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (point : Point) (column : Column)
    (out : alloc.vec.Vec U8) :
    @PV_RunJoin_ClaimList48.cell (types base) (selected base heap box ops) point out column=
      (do let value ← evaluate base heap box ops point column
          alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
            (Array.to_slice (PV_RunJoin_FlatBytes35.wire value))) := by
  unfold PV_RunJoin_ClaimList48.cell evaluate
  rw [show @aspis_core.r0.encoder.eval_message (types base) (selected base heap box ops)=
    @aspis_core.r0.encoder.eval_message (types base) (@ProverRwP6BodyCandidate.selected (types base) ops)
    from PV_RunJoin_ClaimFields48.evaluator base heap box ops]
  apply congrArg (Aeneas.Std.bind _)
  funext value
  rw [show @aspis_core.field.wide_exact.WideExact.to_le_bytes (types base)
    (selected base heap box ops) value=ok (PV_RunJoin_FlatBytes35.wire value)
    from PV_RunJoin_ClaimFields48.serializer base heap box ops value]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_ClaimProducerCell48
