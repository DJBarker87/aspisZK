import NDM_ProjectionRef.Funs
import NDM_CommonCarrier
set_option autoImplicit false
namespace NDM_ProjectionLaw
open Aeneas Aeneas.Std Result

theorem identity {T : Type} (value : T) : NDM_ProjectionRef.identity_ref value=ok value := rfl

/-- Exact projection reference values; no native heap association is assumed discharged. -/
theorem projected (a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
 (c : NDM_CommonCarrier.Candidate) :
 (do let p ← NDM_ProjectionRef.identity_ref (NDM_CommonCarrier.project (NDM_CommonCarrier.value a c))
     ok p) = NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root a.live_snapshot c := rfl

#print axioms identity
#print axioms projected
end NDM_ProjectionLaw
