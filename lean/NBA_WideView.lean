import NBA_Carriers
import SelectedWideViewPreparedEntryV1
set_option autoImplicit false
namespace AspisR1.NBA_WideView
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge

theorem inactive (proof semantic y1 : Slice U8)
    (v : AspisR1SelectedWideViewV1.verifier.View)
    (call : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v)) :
    LPi_FieldValues.canonE (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView v).inactive) := by
  apply (NBA_Carriers.canonical _).mpr
  exact AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 v call

#print axioms inactive
end AspisR1.NBA_WideView
