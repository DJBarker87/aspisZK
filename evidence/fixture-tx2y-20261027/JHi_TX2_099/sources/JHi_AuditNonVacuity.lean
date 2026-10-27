import JHi_Reconstruction
import JHg_DomainRepair
set_option autoImplicit false
namespace AspisR1.JHi_LocalNonVacuity
open Aeneas Aeneas.Std Result
/-- A concrete source-reconstruction witness on the corrected record.
This does not assert authentication, either wrapper's acceptance or headline
hypothesis inhabitance. -/
theorem source : ∃ accounts : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts,
    accounts=JHg_AccountValues.value ∧
    JHf_ReconstructionSlot.source JHd_RequestCarrier.actual accounts JHd_ScanValue.candidate=
      ok (.Ok JGx_RealStatement.value) :=
  ⟨JHg_AccountValues.value,rfl,JHi_Reconstruction.source⟩
#print axioms source
end AspisR1.JHi_LocalNonVacuity
#print axioms AspisR1.JHg_DomainRepair.inhabited
set_option pp.proofs false
#print AspisR1.JHi_LocalNonVacuity.source
