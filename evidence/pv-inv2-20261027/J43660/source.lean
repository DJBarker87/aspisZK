import R1Z.PV_Inv_GuardAllSites
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_PreGuard
open R0P R0Z.HonestValidity
variable {K : Type} [Field K] [DecidableEq K]

/-- Successful static-values/masks interpretation of host_semantic no_pole.
P_static_values and P_active_masks identify the actual source arrays; this
reference alone is not an extraction of the installed callback. -/
def noPoleRef (t : Trace K) (lambda chi : K) : Bool :=
  PV_Inv_Scan.scan chi true (PV_Inv_GuardAllSites.sites t lambda)

theorem source_equation (t : Trace K) (lambda chi : K) :
    noPoleRef t lambda chi = true ↔ NoPole t lambda chi := by
  rw [noPoleRef,PV_Inv_Scan.scan_iff]
  simpa only [true_and] using PV_Inv_GuardAllSites.sites_clear t lambda chi

#print axioms source_equation
end R1Z.PV_Inv_PreGuard
