import R1Z.PV_RunJoin_MultilinearEval69
import R1Z.PV_RunJoin_NativeClaimsApi69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeMultilinear69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (column : Slice Q) (point : Array Q 10#usize) (size : column.length=1024) :
    ∃ out,@aspis_statement.constraints_v4.multilinear_evaluate_qm31 (types base)
      (opsNative base heap box ops runtime world) column point=ok (some out) := by
  rw [PV_RunJoin_NativeClaimsApi69.multilinear]
  obtain ⟨out,ho⟩ := PV_RunJoin_MultilinearEval69.complete
    (PV_B3_Install222.sliceMap PV_B3_Install222.intoCopy column)
    (PV_B3_ArrayCarrier.arrayMap PV_B3_Install222.intoCopy point)
    (by change (column.val.map PV_B3_Install222.intoCopy).length=1024;rw [List.length_map];exact size)
  exact ⟨PV_B3_Install222.fromCopy out,by
    unfold PV_B3_Install222.callback
    rw [ho]
    rfl⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeMultilinear69
