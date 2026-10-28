import R1Z.ProverRwSuccessNativeNormalizeWord
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativeNormalize
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
abbrev source := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31
def normalized (x : Q) : Q :=
  ⟨⟨ProverCommitNativeOps47.normalizeWord x.c0.a,ProverCommitNativeOps47.normalizeWord x.c0.b⟩,
   ⟨ProverCommitNativeOps47.normalizeWord x.c1.a,ProverCommitNativeOps47.normalizeWord x.c1.b⟩⟩
theorem native (x : Q) : source x=.ok (normalized x) := by
  simp only [source,ProverRwSuccessNativePorts.aspis_core.field.wide_exact.canonical_qm31,
    ProverRwSuccessNativeNormalizeWord.word,bind_tc_ok]
  rfl

theorem retained (x : Q) : ProverRwSuccessWideSource.normalize x=.ok (normalized x) := by
  simp only [ProverRwSuccessWideSource.normalize,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1ProducerRelease47.field.P,toQ,toC,
    ProverCommitNativeOps47.rem_source,bind_tc_ok,ProverRwDictionaryTower.mapResult,fromQ,fromC]
  rfl

theorem transport (x : Q) : source x=ProverRwSuccessWideSource.normalize x :=
  (native x).trans (retained x).symm

theorem construct (a b : Q) :
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.new a b=
      ProverRwSuccessWideSource.construct a b := by
  simp only [ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.new,
    ProverRwSuccessWideSource.construct,transport]
#print axioms native
#print axioms retained
#print axioms transport
#print axioms construct
end R1Z.ProverRwSuccessNativeNormalize
