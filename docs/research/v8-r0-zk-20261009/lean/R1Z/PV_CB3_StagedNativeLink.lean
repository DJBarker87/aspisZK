import R1Z.PV_CB3_StagedFields
import R1Z.ProverRwSuccessNativeNormalize
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedNativeLink
open Aeneas Aeneas.Std Result ProverRwFull
namespace F
abbrev P := PV_CB3_StagedFields.aspis_core.field.P
abbrev sub := PV_CB3_StagedFields.aspis_core.field.ct.subtract_p
abbrev reduce := PV_CB3_StagedFields.aspis_core.field.ct.reduce64
abbrev word := PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
abbrev canonical := PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31
abbrev construct := PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
end F
namespace N
abbrev P := ProverRwSuccessNativePorts.aspis_core.field.P
abbrev sub := ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
abbrev reduce := ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
abbrev word := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
abbrev canonical := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31
abbrev construct := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.new
end N

theorem constant : F.P = N.P := by
  simp only [F.P,N.P,PV_CB3_StagedFields.aspis_core.field.P,
    ProverRwSuccessNativePorts.aspis_core.field.P,AspisR1ProducerRelease47.field.P]

theorem subtract (x : U32) : F.sub x = N.sub x := by
  simp only [F.sub,N.sub,PV_CB3_StagedFields.aspis_core.field.ct.subtract_p,
    ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p,← constant]

theorem reduce (x : U64) : F.reduce x = N.reduce x := by
  simp only [F.reduce,N.reduce,PV_CB3_StagedFields.aspis_core.field.ct.reduce64,
    ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64,← constant,subtract]

theorem word (x : U32) : F.word () x = N.word () x := by
  simp only [F.word,N.word,
    PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    reduce]

theorem canonical (x : aspis_core.field.QM31) : F.canonical x = N.canonical x := by
  simp only [F.canonical,N.canonical,
    PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31,word]

theorem construct (a b : aspis_core.field.QM31) : F.construct a b = N.construct a b := by
  simp only [F.construct,N.construct,PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.new,canonical]
#print axioms constant
#print axioms subtract
#print axioms reduce
#print axioms word
#print axioms canonical
#print axioms construct
end R1Z.PV_CB3_StagedNativeLink
