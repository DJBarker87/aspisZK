import S9BodyPrefixWitnessV1
import S3S9TransparentFoldS2InstanceV1
import S9HighTermSourceCellRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9BodyPrefixScalarVectorV1

open AspisR1S9HelperP6
open AspisR1S9BodyPrefixSemanticsV1

abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev E := AspisWideTower.WideExact
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev CurrentDecode := AspisR1S9CurrentFieldOpsV1.decode
abbrev TraceDecode := AspisR1S9HighTermsTraceV1.decW
abbrev Quarter := AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER
abbrev Base (a : Array W (4#usize)) : Fin 4 → E :=
  fun j => TraceDecode (AspisR1.S9ArrayWriteScheduleRootV1.cells a j)
abbrev Seed (q : Q) : E :=
  algebraMap ExactQM E (AspisR1CurrentWide.Proof.decodeQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q))

private theorem current_decode_eq_trace_decode (x : W) :
    CurrentDecode x = TraceDecode x := by
  change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE x) =
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
  rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]

/-- The scalar-factor result's four recorded reads are the exact four cells
of the source `ap0` array. Their ordering is `PERM`; the `readVector` adapter
then exposes precisely the `perm`-indexed vector used by the S2 polynomial. -/
theorem scalar_factor_vector_meaning
    (ap0 : Array W (4#usize)) (q1 : Array Q (4#usize))
    (low : W) (q : Q)
    (hmeaning : AspisR1S9TwoCallScalarMeaningV2.ScalarMeaning ap0 q1 low q) :
    TraceDecode low =
      AspisR1.S2LibraFactoredIdentity.scalar
        (AspisR1.S2LibraFactoredIdentity.scaled (Base ap0) Quarter)
        (Seed q) := by
  obtain ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, q0, q1v, q2, q3,
      hperm0, hp0, hq0, hperm1, hp1, hq1, hperm2, hp2, hq2, hperm3, hp3, hq3,
      hvalue⟩ := hmeaning
  have hj0 : j0 = 0#usize := Result.ok.inj
    (hperm0.symm.trans AspisR1S9TransparentFoldS2InstanceV1.perm_reads.1)
  have hj1 : j1 = 3#usize := Result.ok.inj
    (hperm1.symm.trans AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.1)
  have hj2 : j2 = 2#usize := Result.ok.inj
    (hperm2.symm.trans AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.1)
  have hj3 : j3 = 1#usize := Result.ok.inj
    (hperm3.symm.trans AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.2)
  subst j0; subst j1; subst j2; subst j3
  have hc0 := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
    ap0 0#usize p0 (by decide) hp0
  have hc1 := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
    ap0 3#usize p1 (by decide) hp1
  have hc2 := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
    ap0 2#usize p2 (by decide) hp2
  have hc3 := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
    ap0 1#usize p3 (by decide) hp3
  have hp0cell : p0 = AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 0 := by
    simpa [AspisR1.S9HighTermPolynomialMeaningRootV1.cell] using hc0.symm
  have hp1cell : p1 = AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 3 := by
    simpa [AspisR1.S9HighTermPolynomialMeaningRootV1.cell] using hc1.symm
  have hp2cell : p2 = AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 2 := by
    simpa [AspisR1.S9HighTermPolynomialMeaningRootV1.cell] using hc2.symm
  have hp3cell : p3 = AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 1 := by
    simpa [AspisR1.S9HighTermPolynomialMeaningRootV1.cell] using hc3.symm
  have hvec :
      (fun i : Fin 4 => AspisR1S9TransparentFoldS2InstanceV1.readVector
        (CurrentDecode p0) (CurrentDecode p3) (CurrentDecode p2) (CurrentDecode p1) i) =
      Base ap0 := by
    funext i
    fin_cases i
    · change CurrentDecode p0 = TraceDecode
        (AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 0)
      rw [current_decode_eq_trace_decode, hp0cell]
    · change CurrentDecode p3 = TraceDecode
        (AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 1)
      rw [current_decode_eq_trace_decode, hp3cell]
    · change CurrentDecode p2 = TraceDecode
        (AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 2)
      rw [current_decode_eq_trace_decode, hp2cell]
    · change CurrentDecode p1 = TraceDecode
        (AspisR1.S9ArrayWriteScheduleRootV1.cells ap0 3)
      rw [current_decode_eq_trace_decode, hp1cell]
  have hvecFun := hvec
  calc
    TraceDecode low = CurrentDecode low := (current_decode_eq_trace_decode low).symm
    _ = AspisR1.S2LibraFactoredIdentity.scalar
        (AspisR1.S2LibraFactoredIdentity.scaled
          (fun i : Fin 4 => AspisR1S9TransparentFoldS2InstanceV1.readVector
            (CurrentDecode p0) (CurrentDecode p3) (CurrentDecode p2) (CurrentDecode p1) i)
          Quarter)
        (Seed q) := by
          change AspisR1CurrentWide.Proof.decodeWide
              (AspisR1S9CurrentFieldOpsV1.toE low) =
            AspisR1.S2LibraFactoredIdentity.scalar
              (AspisR1.S2LibraFactoredIdentity.scaled
                (fun i : Fin 4 => AspisR1S9TransparentFoldS2InstanceV1.readVector
                  (AspisR1S9CurrentFieldOpsV1.decode p0)
                  (AspisR1S9CurrentFieldOpsV1.decode p3)
                  (AspisR1S9CurrentFieldOpsV1.decode p2)
                  (AspisR1S9CurrentFieldOpsV1.decode p1) i)
                (AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER))
              (algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact
                (AspisR1CurrentWide.Proof.decodeQM
                  (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)))
          exact hvalue
    _ = AspisR1.S2LibraFactoredIdentity.scalar
        (AspisR1.S2LibraFactoredIdentity.scaled (Base ap0) Quarter)
        (Seed q) := by rw [hvecFun]

#print axioms scalar_factor_vector_meaning

end AspisR1S9BodyPrefixScalarVectorV1
