import R1Z.PV_RunJoin_NominalTraceData
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NominalCompiledData
open PV_RunJoin_NominalLeafData PV_RunJoin_NominalTraceData
abbrev SourceTransition := BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev TargetTransition (base : ProverRwFull.ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (PDict_CodecDictionary.native base)
abbrev SourceCompiled := BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev TargetCompiled (base : ProverRwFull.ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (PDict_CodecDictionary.native base)

def transition (base : ProverRwFull.ExternalTypes) (s : SourceTransition) : TargetTransition base := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact
  ⟨snapshot s.live_snapshot,afterstate s.candidate_afterstate⟩
def unTransition (base : ProverRwFull.ExternalTypes) (s : TargetTransition base) : SourceTransition := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact
  ⟨unSnapshot s.live_snapshot,unAfterstate s.candidate_afterstate⟩

def compiled (base : ProverRwFull.ExternalTypes) (s : SourceCompiled) : TargetCompiled base := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact {
  trace := trace base s.trace
  semantic_c1 := foundation s.semantic_c1
  public_statement := transition base s.public_statement
  }

def unCompiled (base : ProverRwFull.ExternalTypes) (s : TargetCompiled base) : SourceCompiled := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact {
  trace := unTrace base s.trace
  semantic_c1 := unFoundation s.semantic_c1
  public_statement := unTransition base s.public_statement
  }

theorem transition_roundtrip (base : ProverRwFull.ExternalTypes) (s : SourceTransition) : unTransition base (transition base s) = s := rfl

theorem compiled_roundtrip (base : ProverRwFull.ExternalTypes) (s : SourceCompiled) : unCompiled base (compiled base s) = s := by
  cases s with
  | mk trace semantic publicStatement =>
    simp only [compiled,unCompiled,trace_roundtrip,foundation_roundtrip,transition_roundtrip]

/-- All merged semantic columns are literally preserved; no trace equality
with a different model is assumed by this nominal carrier translation. -/
theorem semantic_columns (base : ProverRwFull.ExternalTypes) (s : SourceCompiled) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    (compiled base s).semantic_c1.c1 = s.semantic_c1.c1 := rfl

theorem public_snapshot (base : ProverRwFull.ExternalTypes) (s : SourceCompiled) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    (compiled base s).public_statement.live_snapshot.current_root = s.public_statement.live_snapshot.current_root := rfl

#print axioms transition_roundtrip
#print axioms compiled_roundtrip
#print axioms semantic_columns
#print axioms public_snapshot
end R1Z.PV_RunJoin_NominalCompiledData
