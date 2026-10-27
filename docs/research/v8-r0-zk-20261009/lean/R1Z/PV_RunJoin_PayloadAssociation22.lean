import R1Z.PV_RunJoin_UniversalBuild22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PayloadAssociation22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped

/-- A carrier diagnostic only. This changes caller-supplied cached trace
metadata; it is not the result returned by the compiler on these arguments. -/
def flip : pair_trace.PoolV1PairTraceVariantV1 → pair_trace.PoolV1PairTraceVariantV1
  | .PrivateTransfer => .Withdrawal
  | .Withdrawal => .PrivateTransfer

def altered (i : Input) : Input :=
  {i with compiled := {i.compiled with trace := {i.compiled.trace with variant := flip i.compiled.trace.variant}}}

theorem run_preserved (i : Input) : @run E R (altered i) = @run E R i := rfl
#print axioms run_preserved

theorem public_preserved (i : Input) : publicInput (altered i) = publicInput i := rfl
#print axioms public_preserved

theorem records_preserved (i : Input) :
    PV_RunJoin_UniversalBuild22.records (altered i) = PV_RunJoin_UniversalBuild22.records i := rfl
#print axioms records_preserved

theorem payload_ne (i : Input) : (altered i).compiled ≠ i.compiled := by
  intro same
  have hv := congrArg (fun out : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 => out.trace.variant) same
  change flip i.compiled.trace.variant = i.compiled.trace.variant at hv
  cases h : i.compiled.trace.variant <;> simp [h,flip] at hv
#print axioms payload_ne

theorem no_return (i : Input) (success : @run E R i = ok (.Ok i.compiled)) :
    @run E R (altered i) ≠ ok (.Ok (altered i).compiled) := by
  intro returned
  rw [run_preserved,success] at returned
  exact payload_ne i (core.result.Result.Ok.inj (Result.ok.inj returned)).symm
#print axioms no_return

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem admission_preserved (i : Input) :
    PV_RunJoin_UniversalBuild22.Admission (K := K) (altered i) ↔
      PV_RunJoin_UniversalBuild22.Admission (K := K) i := by
  unfold PV_RunJoin_UniversalBuild22.Admission
  rw [public_preserved,records_preserved]
#print axioms admission_preserved

/-- Mathematical admission of raw data cannot by itself imply association of
an arbitrary caller-supplied cached payload with the actual returned result.
This refutes that candidate totality law conditional on any admitted successful
input. It is NOT a counterexample to V153 on actual returned compiler outputs. -/
theorem admission_does_not_fix_payload (i : Input)
    (admitted : PV_RunJoin_UniversalBuild22.Admission (K := K) i)
    (success : @run E R i = ok (.Ok i.compiled)) :
    ∃ j : Input, PV_RunJoin_UniversalBuild22.Admission (K := K) j ∧
      @run E R j ≠ ok (.Ok j.compiled) :=
  ⟨altered i,(admission_preserved i).mpr admitted,no_return i success⟩
#print axioms admission_does_not_fix_payload
end R1Z.PV_RunJoin_PayloadAssociation22
