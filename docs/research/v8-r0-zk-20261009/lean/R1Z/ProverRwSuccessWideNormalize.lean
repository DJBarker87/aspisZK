import R1Z.ProverRwSuccessWideSource
import R1Z.ProverCommitNativeOps47
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWideNormalize
open Aeneas Aeneas.Std Result
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
abbrev input := ProverRwSuccessQuarticInverseExact.input

theorem word_fixed (x : U32) (hx : x.val<2147483647) :
    ProverCommitNativeOps47.normalizeWord x=x := by
  apply UScalar.eq_of_val_eq
  rw [ProverCommitNativeOps47.normalize_val,Nat.mod_eq_of_lt hx]

theorem fixed (x : Old.Q) (hx : Canonical x) :
    ProverRwSuccessWideSource.normalize (input x)=.ok (input x) := by
  have raw (v : U32) (hv : v.val<2147483647) :
      (v % (2147483647#u32) : Result U32)=.ok v := by
    rw [ProverCommitNativeOps47.rem_source,word_fixed v hv]
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
    (AspisR1ProducerRelease47.field.wide_exact.canonical_qm31 (ProverCommitNativeQ48.source x))=
    .ok (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x))
  simp only [AspisR1ProducerRelease47.field.wide_exact.canonical_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1ProducerRelease47.field.P,ProverCommitNativeQ48.source,
    ProverCommitRelease47.convQ,ProverCommitRelease47.convC,fromQ,fromC,
    raw x.c0.a hx.1.1,raw x.c0.b hx.1.2,raw x.c1.a hx.2.1,raw x.c1.b hx.2.2,
    bind_tc_ok,ProverRwDictionaryTower.mapResult]

theorem construct (a b : Old.Q) (ha : Canonical a) (hb : Canonical b) :
    ProverRwSuccessWideSource.construct (input a) (input b)=.ok ⟨input a,input b⟩ := by
  unfold ProverRwSuccessWideSource.construct
  rw [fixed a ha]
  simp only [bind_tc_ok]
  rw [fixed b hb]
  rfl
#print axioms word_fixed
#print axioms fixed
#print axioms construct
end R1Z.ProverRwSuccessWideNormalize
