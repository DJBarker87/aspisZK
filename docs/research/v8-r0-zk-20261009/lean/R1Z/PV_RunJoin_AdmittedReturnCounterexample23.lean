import R1Z.PV_RunJoin_AdmittedCarrier23
import R1Z.PV_RunJoin_PayloadAssociation22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AdmittedReturnCounterexample23
open Aeneas Aeneas.Std Result PV_Src_NativeInput
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exact admitted raw input with the original transfer call arguments and
public statement. Only cached trace.variant is flipped to Withdrawal. -/
def counterexample : Input :=
  PV_RunJoin_PayloadAssociation22.altered PV_RunJoin_AdmittedCarrier23.transfer

theorem admitted : PV_RunJoin_UniversalBuild22.Admission (K := K) counterexample :=
  (PV_RunJoin_PayloadAssociation22.admission_preserved _).mpr
    PV_RunJoin_AdmittedCarrier23.transfer_admitted
#print axioms admitted

/-- The compiler still succeeds with the original output. This distinguishes
success of the call from equality to an arbitrary cached payload. -/
theorem actual_return : @run E R counterexample =
    ok (.Ok PV_RunJoin_AdmittedCarrier23.transfer.compiled) :=
  (PV_RunJoin_PayloadAssociation22.run_preserved _).trans
    PV_RunJoin_AdmittedCarrier23.transfer_return
#print axioms actual_return

theorem not_cached_return : @run E R counterexample ≠ ok (.Ok counterexample.compiled) :=
  PV_RunJoin_PayloadAssociation22.no_return _ PV_RunJoin_AdmittedCarrier23.transfer_return
#print axioms not_cached_return

/-- Checked counterexample to the precise universal success/association
hypothesis of UniversalBuild22.build_eq. It is not a refutation of the raw
trace equality V153: this particular mutation changes no column. -/
theorem universal_return_false :
    ¬ (∀ i : Input, PV_RunJoin_UniversalBuild22.Admission (K := K) i →
      @run E R i = ok (.Ok i.compiled)) := by
  intro all
  exact not_cached_return (all counterexample admitted)
#print axioms universal_return_false

/-- The failure persists when admission is built into the carrier. -/
theorem admitted_carrier_return_false :
    ¬ (∀ i : PV_RunJoin_AdmittedCarrier23.Admitted (K := K),
      @run E R i.val = ok (.Ok i.val.compiled)) := by
  intro all
  exact not_cached_return (all ⟨counterexample,admitted⟩)
#print axioms admitted_carrier_return_false
end R1Z.PV_RunJoin_AdmittedReturnCounterexample23
