import R1Z.PV_RunJoin_NominalLeafData
import R1Z.PDict_CodecDictionary
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NominalTraceData
open PV_RunJoin_NominalLeafData

abbrev SourceVariant := BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceVariantV1
abbrev TargetVariant := PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1
abbrev SourceOutputs := BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1
abbrev TargetOutputs := PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1
abbrev SourceTrace := BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
abbrev TargetTrace (base : ProverRwFull.ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1 (PDict_CodecDictionary.native base)

def variant : SourceVariant → TargetVariant
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

def unVariant : TargetVariant → SourceVariant
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

def outputs : SourceOutputs → TargetOutputs
  | .PrivateTransfer a b c d e => .PrivateTransfer a b c d e
  | .Withdrawal a b c d => .Withdrawal a b c d

def unOutputs : TargetOutputs → SourceOutputs
  | .PrivateTransfer a b c d e => .PrivateTransfer a b c d e
  | .Withdrawal a b c d => .Withdrawal a b c d

def trace (base : ProverRwFull.ExternalTypes) (s : SourceTrace) : TargetTrace base := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact {
  stable := foundation s.stable
  late := s.late
  variant := variant s.variant
  private_directions := s.private_directions
  value_bits := s.value_bits
  public_outputs := outputs s.public_outputs
  afterstate := afterstate s.afterstate
  }

def unTrace (base : ProverRwFull.ExternalTypes) (s : TargetTrace base) : SourceTrace := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact {
  stable := unFoundation s.stable
  late := s.late
  variant := unVariant s.variant
  private_directions := s.private_directions
  value_bits := s.value_bits
  public_outputs := unOutputs s.public_outputs
  afterstate := unAfterstate s.afterstate
  }

theorem variant_roundtrip (s : SourceVariant) : unVariant (variant s) = s := by cases s <;> rfl
theorem outputs_roundtrip (s : SourceOutputs) : unOutputs (outputs s) = s := by cases s <;> rfl

theorem trace_roundtrip (base : ProverRwFull.ExternalTypes) (s : SourceTrace) : unTrace base (trace base s) = s := by
  cases s with
  | mk stable late variant directions bits outputs afterstate =>
    simp only [trace,unTrace,foundation_roundtrip,variant_roundtrip,outputs_roundtrip,afterstate_roundtrip]

#print axioms variant_roundtrip
#print axioms outputs_roundtrip
#print axioms trace_roundtrip
end R1Z.PV_RunJoin_NominalTraceData
