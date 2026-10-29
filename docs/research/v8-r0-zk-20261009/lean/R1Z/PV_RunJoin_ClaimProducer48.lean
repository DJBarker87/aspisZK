import R1Z.PV_RunJoin_ClaimList48
import R1Z.PV_RunJoin_ClaimFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimProducer48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point W)
open PV_RunJoin_WeightInstalled46

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
      run (fun column => @aspis_core.r0.encoder.eval_message (types base)
        (@ProverRwP6BodyCandidate.selected (types base) ops) _
        (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
          (types base) (selected base heap box ops)) column point) columns out := by
  induction columns generalizing out with
  | nil => rfl
  | cons column tail ih =>
    simp only [PV_RunJoin_ClaimList48.run,PV_RunJoin_ClaimList48.cell,
      aspis_core.r0.encoder.eval_message,PV_RunJoin_ClaimFields48.evaluator,
      aspis_core.field.wide_exact.WideExact.to_le_bytes,
      PV_RunJoin_ClaimFields48.serializer,lift,bind_tc_ok,run,bind_assoc,ih]
#print axioms complete
end R1Z.PV_RunJoin_ClaimProducer48
