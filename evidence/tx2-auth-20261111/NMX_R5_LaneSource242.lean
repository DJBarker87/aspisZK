import NMX_R5_Lane242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_LaneSource242
open Aeneas Aeneas.Std Result AdapterRw

theorem mapped (d : LIBB_NullifierBytes.Digest) :
 NMS_R2N_Interpreted.liftResult (NMX_R5_Lane242.mapped d) =
 NMS_R2N_Interpreted.liftResult (core.result.Result.map_err
  r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
  (NMS_R2LaneModel.result d) ()) := by
 unfold NMX_R5_Lane242.mapped
 rw [NMS_R2LaneModel.source,bind_tc_ok]
#print axioms mapped
end NMX_R5_LaneSource242
end
