import JHg_AccountValues
import JHf_OffsetModel
import JFs_PublicComparisons
set_option autoImplicit false
namespace AspisR1.JHg_DomainRepair
open Aeneas Aeneas.Std Result

theorem changed : JHg_AccountValues.domain≠JHf_DomainBytes.master := by
  rw [JHg_AccountValues.domain_target]
  intro same
  exact JHf_DomainBytes.mismatch same.symm
#print axioms changed

theorem guard : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JFs_PaymentValue.common.deployment_domain JHg_AccountValues.value.live_snapshot.deployment_domain=
      ok false := by
  rw [JHg_AccountValues.live_domain]
  exact JFs_PublicComparisons.domain
#print axioms guard

/-- Necessary domain hypotheses are now jointly inhabited. This is not a
complete authenticated return, reconstruction, or headline witness. -/
theorem inhabited : ∃ a : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts,
    a.master.identity.deployment_domain=JHg_AccountValues.domain ∧
    a.live_snapshot.deployment_domain=JFu_PublicBindings.domain ∧
    a.checkpoint.deployment_domain=JHg_AccountValues.domain :=
  ⟨JHg_AccountValues.value,rfl,JHg_AccountValues.live_domain,rfl⟩
#print axioms inhabited
end AspisR1.JHg_DomainRepair
