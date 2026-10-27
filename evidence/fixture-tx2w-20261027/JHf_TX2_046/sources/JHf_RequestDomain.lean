import JHd_RequestCarrier
import JHf_DomainBytes
set_option autoImplicit false
namespace AspisR1.JHf_RequestDomain
open Aeneas Aeneas.Std Result

def value : Array U8 32#usize := match JHd_RequestCarrier.actual.«public» with
  | .PrivateTransfer p=>p.deployment_domain
  | .Withdrawal p=>p.deployment_domain

theorem public : value=JFt_SnapshotValue.value.deployment_domain := rfl
#print axioms public

theorem mismatch : JHf_DomainBytes.master≠value := by
  rw [public]
  exact JHf_DomainBytes.mismatch
#print axioms mismatch

theorem compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    value JHf_DomainBytes.master=ok true := rfl
#print axioms compare
end AspisR1.JHf_RequestDomain
