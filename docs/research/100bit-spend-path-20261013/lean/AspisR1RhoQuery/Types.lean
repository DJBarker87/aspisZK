import AspisR1RhoAccumulate.Types
namespace AspisR1RhoQuery
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := AspisR1RhoAccumulate.aspis_core.field.M31
abbrev aspis_core.field.CM31 := AspisR1RhoAccumulate.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := AspisR1RhoAccumulate.aspis_core.field.QM31
abbrev aspis_core.field.WideExact := AspisR1RhoAccumulate.aspis_core.field.WideExact
abbrev aspis_core.circle.SecureCirclePoint := AspisR1RhoAccumulate.aspis_core.circle.SecureCirclePoint
abbrev transport.Variant := AspisR1RhoAccumulate.transport.Variant
abbrev verifier.Prepared := AspisR1RhoAccumulate.verifier.Prepared
abbrev verifier.Accumulator := AspisR1RhoAccumulate.verifier.Accumulator
abbrev BatchedWeights := AspisR1RhoAccumulate.BatchedWeights
structure aspis_core.Digest32 (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  digest : Self → (Slice (Slice Std.U8)) → Result (Array Std.U8 32#usize)

inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error

/-- [aspis_r1_cu_gamma::verifier::Phase]
    Source: 'lib.rs', lines 841:0-841:152
    Visibility: public -/
inductive verifier.Phase where
| Parsed : verifier.Phase
| Semantic : verifier.Phase
| SemanticPart : Std.U8 → verifier.Phase
| Prepare : verifier.Phase
| CheckpointRead : verifier.Phase
| Merkle : Std.Usize → verifier.Phase
| Query : Std.Usize → verifier.Phase
| QueryPart : Std.Usize → Std.U8 → verifier.Phase
| CheckpointWrite : verifier.Phase
| Relation : verifier.Phase
| Final : verifier.Phase

/-- [aspis_r1_cu_gamma::verifier::View]
    Source: 'lib.rs', lines 843:0-847:1
    Visibility: public -/
structure verifier.View where
  variant : transport.Variant
  semantic : Slice Std.U8
  y1 : Slice Std.U8
  inactive : aspis_core.field.WideExact
  round0 : Slice Std.U8
  folded_root : Option (Array Std.U8 32#usize)
  round1 : Slice Std.U8
  final_message : Slice Std.U8
  query_bytes : Slice Std.U8

structure QueryGeometry where
  start : Std.Usize
  inverses : alloc.vec.Vec (Array aspis_core.field.M31 5#usize)
  line_z : alloc.vec.Vec aspis_core.field.M31


end AspisR1RhoQuery
