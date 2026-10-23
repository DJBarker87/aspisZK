import S9CombinedWideMulQM31CurrentOuterV1
import S9CurrentCanonicalizerTotalV1
import ExtractedCurrentQM31Exact
import S9ResultSuccessReflectionV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CombinedWideMulQM31HelperTotalExactV1

abbrev SrcQ := AspisR1S9GeneratedCombinedQMResultV1.SourceQM
abbrev SrcW := AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact
abbrev CurQ := AspisR1CurrentWide.field.QM31
abbrev CurW := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev toCurrentQM := AspisR1S9QMSquareCanonicalMapV1.mapQM
abbrev toCurrentWide := AspisR1S9CombinedWideMulQM31CurrentOuterV1.toCurrentWide
def mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private def fromOldQM (x : AspisR1CurrentWide.Proof.Old.QM31) : CurQ :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

private theorem toQM_fromOldQM (x : AspisR1CurrentWide.Proof.Old.QM31) :
    AspisR1CurrentWide.Proof.toQM (fromOldQM x) = x := by cases x <;> rfl

private theorem current_qm_mul_total_exact (x y : CurQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM x)
    (hy : AspisR1CurrentWide.Proof.CanonicalQM y) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM z ∧
      AspisR1CurrentWide.Proof.decodeQM z =
        AspisR1CurrentWide.Proof.decodeQM x * AspisR1CurrentWide.Proof.decodeQM y := by
  obtain ⟨raw, hraw, hcan, hdecode⟩ :=
    AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact
      (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) hx hy
  have hsame := AspisR1CurrentWide.Proof.qm_mul_same x y
  rw [hraw] at hsame
  refine ⟨fromOldQM raw, ?_, ?_, ?_⟩
  · cases hmul : AspisR1CurrentWide.field.QM31.mul x y with
    | fail e => simp [hmul] at hsame
    | div => simp [hmul] at hsame
    | ok z =>
        have hz : AspisR1CurrentWide.Proof.toQM z = raw := by
          simpa [hmul, bind_tc_ok] using hsame
        have hback : fromOldQM (AspisR1CurrentWide.Proof.toQM z) = z := by cases z <;> rfl
        have hzback : z = fromOldQM raw := by
          calc
            z = fromOldQM (AspisR1CurrentWide.Proof.toQM z) := hback.symm
            _ = fromOldQM raw := congrArg fromOldQM hz
        exact congrArg Result.ok hzback
  · change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM
      (AspisR1CurrentWide.Proof.toQM (fromOldQM raw))
    rw [toQM_fromOldQM]
    exact hcan
  · change AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1CurrentWide.Proof.toQM (fromOldQM raw)) = _
    rw [toQM_fromOldQM]
    exact hdecode

private theorem current_wide_mul_qm31_total_exact (x : CurW) (q : CurQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide x) :
    ∃ q' z, AspisR1CurrentWide.field.wide_exact.canonical_qm31 q = .ok q' ∧
      AspisR1CurrentWide.Proof.CanonicalQM q' ∧
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31 x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide z ∧
      AspisR1CurrentWide.Proof.decodeWide z =
        ⟨AspisR1CurrentWide.Proof.decodeQM x.c0 * AspisR1CurrentWide.Proof.decodeQM q',
         AspisR1CurrentWide.Proof.decodeQM x.c1 * AspisR1CurrentWide.Proof.decodeQM q'⟩ := by
  obtain ⟨q', hcanon, hqcan⟩ :=
    AspisR1S9CurrentCanonicalizerTotalV1.canonicalizer_total_canonical q
  obtain ⟨a, ha, hacan, hadeca⟩ := current_qm_mul_total_exact x.c0 q' hx.1 hqcan
  obtain ⟨b, hb, hbcan, hadecb⟩ := current_qm_mul_total_exact x.c1 q' hx.2 hqcan
  let z : CurW := ⟨a, b⟩
  refine ⟨q', z, hcanon, hqcan, ?_, ?_, ?_⟩
  · unfold AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
    rw [hcanon]
    simp only [bind_tc_ok]
    rw [ha]
    simp only [bind_tc_ok]
    rw [hb]
    rfl
  · exact ⟨hacan, hbcan⟩
  · unfold AspisR1CurrentWide.Proof.decodeWide
    exact QuadraticAlgebra.ext hadeca hadecb

/-- The extracted WideExact call is total on a canonical mapped left operand,
with no canonicality premise on the right operand. The returned q' records the
four actual remainder results; the exact decode uses that normalized value. -/
theorem combined_wide_mul_qm31_total_exact
    (x : SrcW) (q : SrcQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide x)) :
    ∃ q' z,
      AspisR1CurrentWide.field.wide_exact.canonical_qm31 (toCurrentQM q) = .ok q' ∧
      AspisR1CurrentWide.Proof.CanonicalQM q' ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (toCurrentWide z) =
        ⟨AspisR1CurrentWide.Proof.decodeQM (toCurrentWide x).c0 *
            AspisR1CurrentWide.Proof.decodeQM q',
         AspisR1CurrentWide.Proof.decodeQM (toCurrentWide x).c1 *
            AspisR1CurrentWide.Proof.decodeQM q'⟩ := by
  obtain ⟨q', out, hqcall, hqcan, hout, hcan, hdecode⟩ :=
    current_wide_mul_qm31_total_exact (toCurrentWide x) (toCurrentQM q) hx
  have hm := AspisR1S9CombinedWideMulQM31CurrentOuterV1.combined_wide_mul_qm31_to_current x q hx
  have hs : AspisR1S9SourceResultTransportV1.mapResult toCurrentWide
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) = .ok out :=
    hm.trans hout
  obtain ⟨z, hz, hcur⟩ :=
    (AspisR1S9ResultSuccessReflectionV1.mapResult_ok_iff toCurrentWide
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) out).mp hs
  refine ⟨q', z, hqcall, hqcan, hz, ?_, ?_⟩
  · rw [hcur]
    exact hcan
  · rw [hcur]
    exact hdecode

#print axioms combined_wide_mul_qm31_total_exact

end AspisR1S9CombinedWideMulQM31HelperTotalExactV1
