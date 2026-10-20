import AspisR1RhoReferenceLoop.Types
import AspisR1RhoPowerTail.Types
namespace AspisR1RhoAccumulate
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := AspisR1CuRho.field.M31
abbrev aspis_core.field.CM31 := AspisR1CuRho.field.CM31
abbrev aspis_core.field.QM31 := AspisR1CuRho.field.QM31
abbrev aspis_core.field.WideExact := AspisR1CuRho.field.WideExact
abbrev transport.Variant := AspisR1RhoPowerTail.transport.Variant
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31
abbrev BatchedWeights := AspisR1CuRho.verifier.BatchedWeights
structure verifier.Prepared where
  variant : transport.Variant
  roots : Array (Array Std.U8 32#usize) 2#usize
  gamma : aspis_core.field.WideExact
  kappa : aspis_core.field.WideExact
  alpha : Array aspis_core.field.WideExact 2#usize
  rho : aspis_core.field.QM31
  queries : Array Std.U32 22#usize
  semantic_alpha : Array aspis_core.field.QM31 10#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  claim : aspis_core.field.WideExact
  state : Array Std.U8 32#usize

/-- [aspis_r1_cu_gamma::verifier::Accumulator]
    Source: 'lib.rs', lines 853:0-853:82
    Visibility: public -/
structure verifier.Accumulator where
  weights : alloc.vec.Vec aspis_core.field.QM31
  rhs : aspis_core.field.WideExact
  power : aspis_core.field.QM31
  next : Std.Usize


end AspisR1RhoAccumulate
