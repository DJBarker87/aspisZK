import R1Z.PV_RunJoin_UniversalBuild22
import R1Z.PV_RunJoin_FixtureArguments
import R1Z.PV_RunJoin_TransferPayload20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AdmissionBoundary23
open Aeneas Aeneas.Std Result PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exact raw source instance: input 0, withdrawal output 1, change 0.
The original fixture payload is retained as caller-supplied data. -/
def bad : Input where
  request := .withdrawal {PV_RunJoin_RecordedWithdrawal.publicRecord with amount := 1#u32}
  witness := {witness with pair := {witness.pair with value := 0#u32}}
  change := {withdrawalChange with value := 0#u32}
  laneAnchor := laneAnchor
  snapshot := snapshot
  compiled := PV_RunJoin_TransferPayload20.output

/-- Only the three small value projections are reduced; no hash, bank,
compiler run or recurrence is evaluated. -/
theorem bad_not_admitted : ¬ PV_RunJoin_UniversalBuild22.Admission (K := K) bad := by
  intro h
  have balance := h.1.2.2.1
  change (0 : Nat) = 1 + 0 at balance
  omega
#print axioms bad_not_admitted

/-- The unguarded native prover's Instance is raw Input itself. Membership
in it does not imply the semantic admission needed by toInstance. -/
def bad_source_instance :
    (PV_Src_NativeIdentification.prover (K := K) (fun i : Input => i)
      PV_Src_Transport.transport).Instance := bad

theorem source_instance_not_admitted :
    ¬ PV_RunJoin_UniversalBuild22.Admission (K := K)
      (bad_source_instance (K := K)) := bad_not_admitted
#print axioms source_instance_not_admitted

theorem admission_not_derivable :
    ¬ (∀ w : (PV_Src_NativeIdentification.prover (K := K) (fun i : Input => i)
      PV_Src_Transport.transport).Instance,
      PV_RunJoin_UniversalBuild22.Admission (K := K) w) := by
  intro all
  exact bad_not_admitted (all bad)
#print axioms admission_not_derivable
end R1Z.PV_RunJoin_AdmissionBoundary23
