import R1Z.PV_OptB_SourceRetryStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourcePoleBoundary
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

abbrev Rows := alloc.vec.Vec (Array (Array aspis_core.field.QM31 2#usize) 2#usize)

/-- Exact enclosing source no-pole function after its row extraction, public
mask acquisition and scan. These are explicit P boundaries, not assumptions
installed into the endpoint or the capped trust record. -/
theorem scanned (compiled : Compiled) (lam chi : aspis_core.field.QM31)
    (rows : Rows) (masks : Array U16 64#usize) (clear : Bool)
    (rowLaw : host_semantic.lean_copy_row_values compiled.trace lam = .ok (.Ok rows))
    (maskLaw : aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1 =
      .ok (.Ok masks))
    (mapped : core.result.Result.map_err
      host_semantic.no_pole.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1Error
      (.Ok masks) () = .ok (.Ok masks))
    (scanLaw : ct_pole.all_slots_clear (alloc.vec.Vec.deref rows) masks chi = .ok clear) :
    host_semantic.no_pole compiled lam chi = .ok (.Ok clear) := by
  rw [host_semantic.no_pole,rowLaw]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,maskLaw,
    mapped,core.result.Result.Insts.CoreOpsTry.branch]
  rw [scanLaw]
  rfl

#print axioms scanned
end R1Z.PV_OptB_SourcePoleBoundary
