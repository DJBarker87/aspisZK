import R1Z.ProverRwFullTypes
namespace PV_B2_WeightsNative
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.circle.SecureCirclePoint := ProverRwFull.aspis_core.circle.SecureCirclePoint
abbrev transport.Variant := ProverRwFull.transport.Variant
abbrev verifier.Error := ProverRwFull.verifier.Error
structure host_weights.Weights where
  variant : transport.Variant
  factors : Array (Array (Array aspis_core.field.QM31 4#usize) 5#usize) 5#usize
  points : Array (Array aspis_core.field.QM31 10#usize) 3#usize
  extra : Array aspis_core.field.QM31 2#usize

end PV_B2_WeightsNative
