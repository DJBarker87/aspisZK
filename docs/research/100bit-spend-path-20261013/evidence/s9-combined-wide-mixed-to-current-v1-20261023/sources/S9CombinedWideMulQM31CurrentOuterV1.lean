import S9CombinedQMToCurrentV1
import S9CurrentCanonicalizerTotalV1
import S9QMSquareCanonicalMapV1
import S9SourceResultTransportV1
import S9ResultSuccessReflectionV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CombinedWideMulQM31CurrentOuterV1

abbrev SrcQ := AspisR1S9GeneratedCombinedQMResultV1.SourceQM
abbrev SrcW := AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact
abbrev CurQ := AspisR1CurrentWide.field.QM31
abbrev CurW := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev toCurrentQM := AspisR1S9QMSquareCanonicalMapV1.mapQM

def toCurrentWide (x : SrcW) : CurW := ⟨toCurrentQM x.c0, toCurrentQM x.c1⟩

def mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

theorem combined_wide_mul_qm31_to_current
    (x : SrcW) (q : SrcQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (toCurrentWide x)) :
    mapResult toCurrentWide (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31 x q) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31 (toCurrentWide x) (toCurrentQM q) := by
  have hcanonical := AspisR1S9QMSquareCanonicalMapV1.canonical_qm31_result_map q
  obtain ⟨qcur, hqcur, hqcanonical⟩ :=
    AspisR1S9CurrentCanonicalizerTotalV1.canonicalizer_total_canonical (toCurrentQM q)
  have hcanonicalMap : mapResult toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31 q) =
      AspisR1CurrentWide.field.wide_exact.canonical_qm31 (toCurrentQM q) := by
    have hhead : ∀ r : Result SrcQ,
        mapResult toCurrentQM r =
          AspisR1S9QMSquareCanonicalMapV1.mapResult toCurrentQM r := by
      intro r
      cases r <;> rfl
    rw [hhead]
    exact hcanonical
  have hcanonicalSuccess : mapResult toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31 q) = .ok qcur :=
    hcanonicalMap.trans hqcur
  obtain ⟨qsrc, hsource, hqmap⟩ :=
    (AspisR1S9ResultSuccessReflectionV1.mapResult_ok_iff toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.wide_exact.canonical_qm31 q) qcur).mp
      hcanonicalSuccess
  have hqsrcCanonical : AspisR1CurrentWide.Proof.CanonicalQM (toCurrentQM qsrc) := by
    rw [hqmap]
    exact hqcanonical
  have hmul0 := AspisR1S9CombinedQMToCurrentV1.combined_qm_mul_to_current
    x.c0 qsrc hx.1 hqsrcCanonical
  have hmul1 := AspisR1S9CombinedQMToCurrentV1.combined_qm_mul_to_current
    x.c1 qsrc hx.2 hqsrcCanonical
  change mapResult toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c0 qsrc) =
    AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c0) (toCurrentQM qsrc) at hmul0
  change mapResult toCurrentQM
      (AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c1 qsrc) =
    AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c1) (toCurrentQM qsrc) at hmul1
  rw [hqmap] at hmul0 hmul1
  unfold AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
    AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
  rw [hsource, hqcur]
  simp only [bind_tc_ok]
  change mapResult toCurrentWide (do
      let a ← AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c0 qsrc
      let b ← AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c1 qsrc
      Result.ok ({ c0 := a, c1 := b } : SrcW)) = (do
      let a ← AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c0) qcur
      let b ← AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c1) qcur
      Result.ok ({ c0 := a, c1 := b } : CurW))
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCurrentQM toCurrentWide
    (AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c0 qsrc)
    (AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c0) qcur)
    (fun a => do
      let b ← AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c1 qsrc
      Result.ok ({ c0 := a, c1 := b } : SrcW))
    (fun a => do
      let b ← AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c1) qcur
      Result.ok ({ c0 := a, c1 := b } : CurW))
    hmul0
  intro a
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq toCurrentQM toCurrentWide
    (AspisR1S9SquareMulQMCutV1.field.QM31.mul x.c1 qsrc)
    (AspisR1CurrentWide.field.QM31.mul (toCurrentQM x.c1) qcur)
    (fun b => Result.ok ({ c0 := a, c1 := b } : SrcW))
    (fun b => Result.ok ({ c0 := toCurrentQM a, c1 := b } : CurW))
    hmul1
  intro b
  rfl

#print axioms combined_wide_mul_qm31_to_current

end AspisR1S9CombinedWideMulQM31CurrentOuterV1
