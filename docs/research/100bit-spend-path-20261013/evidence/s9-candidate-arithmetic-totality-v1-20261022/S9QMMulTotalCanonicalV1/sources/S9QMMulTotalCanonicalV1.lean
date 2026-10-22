import KpowersCurrentQMSemanticsV1
import CurrentWideQMField
import ExtractedCurrentQM31Exact
import S4FromFnP6GeneratedInterface
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMMulTotalCanonicalV1

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1

abbrev Q := field.QM31
abbrev CQM := AspisR1CurrentWide.field.QM31

private def fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) : CQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem toQM_fromOld (x : AspisR1CurrentWide.Proof.Old.QM31) :
    AspisR1CurrentWide.Proof.toQM (fromOld x) = x := by cases x <;> rfl

private theorem current_qm_mul_total (x y : CQM)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM x)
    (hy : AspisR1CurrentWide.Proof.CanonicalQM y) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM z := by
  obtain ⟨raw, hraw, hcan, _⟩ :=
    AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact
      (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) hx hy
  have hsame := AspisR1CurrentWide.Proof.qm_mul_same x y
  rw [hraw] at hsame
  refine ⟨fromOld raw, ?_, ?_⟩
  · cases hmul : AspisR1CurrentWide.field.QM31.mul x y with
    | fail e => simp [hmul] at hsame
    | div => simp [hmul] at hsame
    | ok z =>
        have hz : AspisR1CurrentWide.Proof.toQM z = raw := by
          simpa [hmul, bind_tc_ok] using hsame
        have hback : fromOld (AspisR1CurrentWide.Proof.toQM z) = z := by
          cases z <;> rfl
        have hzback : z = fromOld raw := by
          calc
            z = fromOld (AspisR1CurrentWide.Proof.toQM z) := hback.symm
            _ = fromOld raw := congrArg fromOld hz
        exact congrArg Result.ok hzback
  · change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM
      (AspisR1CurrentWide.Proof.toQM (fromOld raw))
    rw [toQM_fromOld]
    exact hcan

/-- The operation underlying the selected concrete QM31 multiplication is
successful and preserves the current canonical-input invariant. This is the
public bridge used to totalize the helper's explicit q12/q3 multiplication
calls; it is derived from the exact extracted QM31 multiplication spec. -/
theorem concrete_qm_mul_total
    (x y : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM x))
    (hy : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM y)) :
    ∃ z, @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM z) := by
  obtain ⟨out, hout, hcan⟩ := current_qm_mul_total
    (helperToCurrentQM x) (helperToCurrentQM y) hx hy
  refine ⟨currentToHelperQM out, ?_, ?_⟩
  · rw [AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current]
    change (do
      let z ← AspisR1CurrentWide.field.QM31.mul
        (helperToCurrentQM x) (helperToCurrentQM y)
      ok (currentToHelperQM z)) = .ok (currentToHelperQM out)
    rw [hout]
    rfl
  · exact hcan

#print axioms concrete_qm_mul_total

end AspisR1S9QMMulTotalCanonicalV1
