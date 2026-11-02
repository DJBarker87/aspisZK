import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.ProverRwSuccessPointsCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeClaimsApi69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem some_ok (q : Q) :
    @core.option.Option.ok_or (types base) (opsNative base heap box ops runtime world)
      Q r1_wire.Error (some q) r1_wire.Error.Public=ok (.Ok q) := by
  rfl

theorem points (point : Array Q 10#usize) :
    ∃ out,@r1_wire.statement_points (types base) (opsNative base heap box ops runtime world) point=ok out := by
  change ∃ out,ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points point=ok out
  exact ProverRwSuccessPointsCaller.source_total point

/-- Binding to the installed copy, keeping the original arbitrary point. -/
theorem multilinear (column : Slice Q) (point : Array Q 10#usize) :
    @aspis_statement.constraints_v4.multilinear_evaluate_qm31 (types base)
      (opsNative base heap box ops runtime world) column point=
      PV_B3_Install222.callback column point := by
  rfl

#print axioms some_ok
#print axioms points
#print axioms multilinear
end R1Z.PV_RunJoin_NativeClaimsApi69
