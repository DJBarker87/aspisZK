import NJY_Roots
import NHJ_DeployedIds
set_option autoImplicit false
noncomputable section
namespace NJY_Install
open Aeneas Aeneas.Std Result
/-- The direct registry/entry decoder realizations in the deployed configuration.
Identity149 is internal. Master/checkpoint helper Results are account errors;
slots48/49 are boxed-wrapper ProgramError Results, outside this job.
This is an installation/realization theorem, not premise removal. -/
def bindDecoders {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
 {missing with adapter := {missing.adapter with
   op31 := NJQ_Canonical.registry
   op32 := NJQ_Canonical.entry}}

/-- Same deployed configuration constructor and carrier as the coherent cohort. -/
theorem actual_slots {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
 (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
 (NHJ_DeployedIds.configuration (bindDecoders missing) devnet indexError reservation).adapter.op31 = NJQ_Canonical.registry ∧
 (NHJ_DeployedIds.configuration (bindDecoders missing) devnet indexError reservation).adapter.op32 = NJQ_Canonical.entry :=
 ⟨rfl,rfl⟩

/-- The coherent digest/error slots are43/44, preserved by decoder installation. -/
theorem digest_error_frame {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :
 (bindDecoders missing).adapter.op43 = missing.adapter.op43 ∧
 (bindDecoders missing).adapter.op44 = missing.adapter.op44 ∧
 (bindDecoders missing).adapter.op48 = missing.adapter.op48 ∧
 (bindDecoders missing).adapter.op49 = missing.adapter.op49 := ⟨rfl,rfl,rfl,rfl⟩
set_option pp.proofs false in
#print actual_slots
#print axioms actual_slots
set_option pp.proofs false in
#print digest_error_frame
#print axioms digest_error_frame
end NJY_Install
