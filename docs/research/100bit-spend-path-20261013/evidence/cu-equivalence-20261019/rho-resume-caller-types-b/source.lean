import AspisR1RhoStage.Types
import AspisR1RhoReader.Types
open Aeneas Aeneas.Std
namespace AspisR1RhoResumeCaller
abbrev aspis_core.field.M31 := AspisR1RhoQuery.aspis_core.field.M31
abbrev aspis_core.field.CM31 := AspisR1RhoQuery.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := AspisR1RhoQuery.aspis_core.field.QM31
abbrev aspis_core.field.WideExact := AspisR1RhoQuery.aspis_core.field.WideExact
abbrev aspis_core.circle.SecureCirclePoint := AspisR1RhoQuery.aspis_core.circle.SecureCirclePoint
abbrev aspis_core.Digest32 := AspisR1RhoQuery.aspis_core.Digest32
abbrev transport.Variant := AspisR1RhoQuery.transport.Variant
abbrev verifier.Error := AspisR1RhoQuery.verifier.Error
abbrev verifier.Prepared := AspisR1RhoQuery.verifier.Prepared
abbrev verifier.Accumulator := AspisR1RhoQuery.verifier.Accumulator
abbrev ResumeReader := AspisR1CuRho.verifier.Reader
structure ResumeBegin where
  r : ResumeReader
  «end» : Std.Usize
  state : Array Std.U8 32#usize
  roots : Array (Array Std.U8 32#usize) 2#usize
  gamma : aspis_core.field.WideExact
  kappa : aspis_core.field.WideExact
  alpha : Array aspis_core.field.WideExact 2#usize

/-- [aspis_r1_cu_gamma::ResumeMiddle]
    Source: 'lib.rs', lines 1088:0-1088:190
    Visibility: public -/
structure ResumeMiddle where
  r : ResumeReader
  queries : Array Std.U32 22#usize
  semantic_alpha : Array aspis_core.field.QM31 10#usize
  z : Array aspis_core.circle.SecureCirclePoint 2#usize
  claim : aspis_core.field.WideExact
  rhs : aspis_core.field.WideExact


end AspisR1RhoResumeCaller
