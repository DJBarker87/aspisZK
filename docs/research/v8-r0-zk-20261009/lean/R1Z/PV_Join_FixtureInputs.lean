import R1Z.PV_Join_LedgerSource
import R1Z.PV_RunJoin_NominalPublicData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_FixtureInputs
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

/-- Field-preserving conversion at the joined caller's actual carrier.
The whole ExternalTypes dictionaries are deliberately not identified. -/
def transition (base : ExternalTypes)
    (t : PV_RunJoin_NominalCompiledData.SourceTransition) :
    @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact ⟨PV_RunJoin_NominalLeafData.snapshot t.live_snapshot,
    PV_RunJoin_NominalLeafData.afterstate t.candidate_afterstate⟩

def trace (base : ExternalTypes) (t : PV_RunJoin_NominalTraceData.SourceTrace) :
    @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact {
    stable := PV_RunJoin_NominalLeafData.foundation t.stable
    late := t.late
    variant := PV_RunJoin_NominalTraceData.variant t.variant
    private_directions := t.private_directions
    value_bits := t.value_bits
    public_outputs := PV_RunJoin_NominalTraceData.outputs t.public_outputs
    afterstate := PV_RunJoin_NominalLeafData.afterstate t.afterstate }

def compiled (base : ExternalTypes) (c : PV_RunJoin_NominalCompiledData.SourceCompiled) :
    @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact ⟨trace base c.trace,PV_RunJoin_NominalLeafData.foundation c.semantic_c1,
    transition base c.public_statement⟩

def publicInput (base : ExternalTypes) (i : PV_Src_NativeInput.Input) :
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact match i.request with
    | .transfer pub _ => .Transfer (PV_RunJoin_NominalPublicData.transfer pub)
        (transition base i.compiled.public_statement)
    | .withdrawal pub => .Withdrawal (PV_RunJoin_NominalPublicData.withdrawal pub)
        (transition base i.compiled.public_statement)

theorem semantic_columns (base : ExternalTypes)
    (c : PV_RunJoin_NominalCompiledData.SourceCompiled) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    (compiled base c).semantic_c1.c1 = c.semantic_c1.c1 := rfl

def inputs (base : ExternalTypes) {N C : Type}
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    PV_RunJoin_LedgerBody.Inputs N C :=
  PV_Join_LedgerSource.inputs base ops
    (fun _ => publicInput base i)
    (fun _ => compiled base i.compiled)
    (fun _ => hash)

/-- Both public and compiled values come from the very same selected compiler
record. Native compiler success is still a separate obligation. -/
theorem same_record (base : ExternalTypes) {N C : Type}
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) (s : PV_Join_LedgerSource.World base N C) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    (inputs base ops hash i).pub s = publicInput base i ∧
    (inputs base ops hash i).compiled s = compiled base i.compiled := ⟨rfl,rfl⟩

theorem body_source (base : ExternalTypes) {N C : Type}
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (inputs base ops hash i))
      (PV_RunJoin_LedgerBody.body schedule unix address (inputs base ops hash i)) :=
  PV_Join_LedgerSource.body_source base ops _ _ _ schedule unix address

#print axioms transition
#print axioms trace
#print axioms compiled
#print axioms publicInput
#print axioms semantic_columns
#print axioms inputs
#print axioms same_record
#print axioms body_source
end R1Z.PV_Join_FixtureInputs
