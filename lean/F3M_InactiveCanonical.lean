import F3K_InactivePhysical
import SelectedWideViewInactiveV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_InactiveCanonical
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation

theorem source (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical
      (AspisR1ClaimPreparedBridge.toClaimE (retainedView view).inactive) := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current proof semantic y1 view accepted
  have canonical := AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 selected call
  rw [← same]
  exact canonical

#print axioms source
end AspisR1.F3M_InactiveCanonical
end
