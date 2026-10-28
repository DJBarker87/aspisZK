import AspisR1ProducerRelease47.Weights49
import R1Z.ProverCommitWideOps48
import R1Z.ProverCommitNativeQ48
import R1Z.ProverCommitNativeOps47
/-! Actual full-width WideExact::mul_qm31, including raw RHS normalization. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWideQM31Scalar49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)

def embed (x : AspisV8R15.ExactTowerBase.QM31Exact) : Exact := ⟨x,0⟩

theorem normalize_source (q : Old.Q) :
    field.wide_exact.canonical_qm31 (ProverCommitNativeQ48.source q)=
      ok (ProverCommitNativeQ48.source (ProverCommitNativeOps47.normalize q)) := by
  simp only [field.wide_exact.canonical_qm31,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    field.P,ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,
    ProverCommitRelease47.convC,fromQ,fromC,ProverCommitNativeOps47.rem_source,bind_tc_ok]
  rfl

theorem value_exact (x : Raw) (q : Old.Q) (hx : canonical x) :
    ∃ z : Raw, field.wide_exact.WideExact.mul_qm31 (source x) (ProverCommitNativeQ48.source q)=
      ok (source z) ∧ canonical z ∧ value z=value x*embed (decode q) := by
  obtain ⟨lo,hlo,hclo,hdlo⟩ := ProverCommitNativeQ48.mul x.1 (ProverCommitNativeOps47.normalize q)
    hx.1 (ProverCommitNativeOps47.normalize_canonical q)
  obtain ⟨hi,hhi,hchi,hdhi⟩ := ProverCommitNativeQ48.mul x.2 (ProverCommitNativeOps47.normalize q)
    hx.2 (ProverCommitNativeOps47.normalize_canonical q)
  refine ⟨(lo,hi),?_,⟨hclo,hchi⟩,?_⟩
  · rw [field.wide_exact.WideExact.mul_qm31,normalize_source]
    simp only [bind_tc_ok]
    change (do
      let lo ← field.QM31.mul (ProverCommitNativeQ48.source x.1)
        (ProverCommitNativeQ48.source (ProverCommitNativeOps47.normalize q))
      let hi ← field.QM31.mul (ProverCommitNativeQ48.source x.2)
        (ProverCommitNativeQ48.source (ProverCommitNativeOps47.normalize q))
      ok {c0:=lo,c1:=hi})=ok (source (lo,hi))
    rw [hlo];simp only [bind_tc_ok,hhi];rfl
  · apply QuadraticAlgebra.ext
    · change decode lo=_
      rw [hdlo,ProverCommitNativeOps47.normalize_decode]
      simp [value,embed]
    · change decode hi=_
      rw [hdhi,ProverCommitNativeOps47.normalize_decode]
      simp [value,embed]

#print axioms normalize_source
#print axioms value_exact
end R1Z.ProverCommitWideQM31Scalar49
