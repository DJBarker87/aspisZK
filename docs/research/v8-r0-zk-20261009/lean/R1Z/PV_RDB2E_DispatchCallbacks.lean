import R1Z.PV_RDB2E_Dispatch
import R1Z.PV_RDB2E_ShaTypedFinal
namespace R1Z.PV_RDB2E_Dispatch
open Aeneas Aeneas.Std Result PV_RDB2E_ShaHandles
set_option autoImplicit false

def select (backend : Backend) (soft shani : State → List U8 → Result State) :
    State → List U8 → Result State :=
  match backend with | .soft => soft | .shani => shani

/-- Branch-complete model law. Neither reachable native backend is erased or
assumed equal to the other by this statement. -/
theorem full_dispatch (backend : Backend) (soft shani : State → List U8 → Result State)
    (f : Frame) (valid : (position f).val<64) :
    (do let after ← finalize (select backend soft shani) f valid;ok (forget after))=
      PV_RDB2D_SHAState.finalize (select backend soft shani) f.core f.buffer (position f) f.output :=
  complete_typed (select backend soft shani) f valid

theorem software_selected (soft shani : State → List U8 → Result State) :
    select .soft soft shani=soft := rfl

theorem shani_selected (soft shani : State → List U8 → Result State) :
    select .shani soft shani=shani := rfl

#print axioms full_dispatch
#print axioms software_selected
#print axioms shani_selected
end R1Z.PV_RDB2E_Dispatch
