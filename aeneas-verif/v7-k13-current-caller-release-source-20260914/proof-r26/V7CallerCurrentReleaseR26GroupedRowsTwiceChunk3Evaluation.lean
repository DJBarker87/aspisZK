import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2Evaluation

/-! # Canonical evaluation certificate for fused chunk three -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3Evaluation

open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3
open V7CallerCurrentReleaseR26GroupedRowsTwiceContributions

abbrev RawQM31 := field.QM31

structure Evaluation
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g3 g4 g5 g6 : CanonicalRaw) : Type where
  coefficientTrace : Chunk3CoefficientTrace
    b0.raw b1.raw b2.raw b3.raw b4.raw b5.raw b6.raw b7.raw
    b8.raw b9.raw b10.raw b11.raw b12.raw b13.raw b14.raw b15.raw
  contributionTrace : Chunk3ContributionTrace groupValues b0.raw
    coefficientTrace.c4 b5.raw b6.raw coefficientTrace.d15
  half1 : CanonicalRaw
  half2 : CanonicalRaw
  half3 : CanonicalRaw
  half4 : CanonicalRaw
  half1Run : field.QM31.half contributionTrace.sum4 = ok half1.raw
  half2Run : field.QM31.half half1.raw = ok half2.raw
  half3Run : field.QM31.half half2.raw = ok half3.raw
  half4Run : field.QM31.half half3.raw = ok half4.raw

noncomputable def evaluation
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g3 g4 g5 g6 : CanonicalRaw)
    (g1Read : Slice.index_usize groupValues 1#usize = ok g1.raw)
    (g3Read : Slice.index_usize groupValues 3#usize = ok g3.raw)
    (g4Read : Slice.index_usize groupValues 4#usize = ok g4.raw)
    (g5Read : Slice.index_usize groupValues 5#usize = ok g5.raw)
    (g6Read : Slice.index_usize groupValues 6#usize = ok g6.raw) :
    Evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 g1 g3 g4 g5 g6 := by
  let c2 := add b1 b2
  let c3 := add c2 b3
  let c4 := add c3 b4
  let d8 := add b7 b8
  let d9 := add d8 b9
  let d10 := add d9 b10
  let d11 := add d10 b11
  let d12 := add d11 b12
  let d13 := add d12 b13
  let d14 := add d13 b14
  let d15 := add d14 b15
  let coefficientTrace : Chunk3CoefficientTrace
      b0.raw b1.raw b2.raw b3.raw b4.raw b5.raw b6.raw b7.raw
      b8.raw b9.raw b10.raw b11.raw b12.raw b13.raw b14.raw b15.raw := {
    c2 := c2.raw, c3 := c3.raw, c4 := c4.raw
    d8 := d8.raw, d9 := d9.raw, d10 := d10.raw, d11 := d11.raw
    d12 := d12.raw, d13 := d13.raw, d14 := d14.raw, d15 := d15.raw
    c2Run := add_run b1 b2, c3Run := add_run c2 b3, c4Run := add_run c3 b4
    d8Run := add_run b7 b8, d9Run := add_run d8 b9
    d10Run := add_run d9 b10, d11Run := add_run d10 b11
    d12Run := add_run d11 b12, d13Run := add_run d12 b13
    d14Run := add_run d13 b14, d15Run := add_run d14 b15 }
  let p3 := mul g3 c4
  let p4 := mul g4 b5
  let p5 := mul g5 b6
  let p6 := mul g6 d15
  let s0 := add zero g1
  let s1 := add s0 p3
  let s2 := add s1 p4
  let s3 := add s2 p5
  let s4 := add s3 p6
  let contributionTrace : Chunk3ContributionTrace groupValues b0.raw c4.raw
      b5.raw b6.raw d15.raw := {
    value1 := g1.raw, value3 := g3.raw, value4 := g4.raw
    value5 := g5.raw, value6 := g6.raw
    product3 := p3.raw, product4 := p4.raw, product5 := p5.raw, product6 := p6.raw
    sum0 := s0.raw, sum1 := s1.raw, sum2 := s2.raw, sum3 := s3.raw, sum4 := s4.raw
    value1Run := g1Read, value3Run := g3Read, value4Run := g4Read
    value5Run := g5Read, value6Run := g6Read
    product3Run := mul_run g3 c4, product4Run := mul_run g4 b5
    product5Run := mul_run g5 b6, product6Run := mul_run g6 d15
    sum0Run := add_run zero g1, sum1Run := add_run s0 p3
    sum2Run := add_run s1 p4, sum3Run := add_run s2 p5, sum4Run := add_run s3 p6 }
  let half1 := half s4
  let half2 := half half1
  let half3 := half half2
  let half4 := half half3
  exact {
    coefficientTrace := coefficientTrace, contributionTrace := contributionTrace
    half1 := half1, half2 := half2, half3 := half3, half4 := half4
    half1Run := half_run s4, half2Run := half_run half1
    half3Run := half_run half2, half4Run := half_run half3 }

theorem output_exact
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g3 g4 g5 g6 : CanonicalRaw)
    (g1Read : Slice.index_usize groupValues 1#usize = ok g1.raw)
    (g3Read : Slice.index_usize groupValues 3#usize = ok g3.raw)
    (g4Read : Slice.index_usize groupValues 4#usize = ok g4.raw)
    (g5Read : Slice.index_usize groupValues 5#usize = ok g5.raw)
    (g6Read : Slice.index_usize groupValues 6#usize = ok g6.raw) :
    let result := evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      b10 b11 b12 b13 b14 b15 g1 g3 g4 g5 g6 g1Read g3Read g4Read g5Read g6Read
    16 * exact result.half4 =
      exact g1 + exact g3 * (exact b1 + exact b2 + exact b3 + exact b4) +
      exact g4 * exact b5 + exact g5 * exact b6 +
      exact g6 * (exact b7 + exact b8 + exact b9 + exact b10 + exact b11 +
        exact b12 + exact b13 + exact b14 + exact b15) := by
  dsimp only
  let result := evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    b10 b11 b12 b13 b14 b15 g1 g3 g4 g5 g6 g1Read g3Read g4Read g5Read g6Read
  change 16 * exact result.half4 = _
  have h4 : exact result.half4 + exact result.half4 = exact result.half3 := by
    simpa [result, evaluation] using half_exact result.half3
  have h3 : exact result.half3 + exact result.half3 = exact result.half2 := by
    simpa [result, evaluation] using half_exact result.half2
  have h2 : exact result.half2 + exact result.half2 = exact result.half1 := by
    simpa [result, evaluation] using half_exact result.half1
  let c4 := add (add (add b1 b2) b3) b4
  let d15 := add (add (add (add (add (add (add (add b7 b8) b9) b10) b11) b12) b13) b14) b15
  let numerator := add (add (add (add (add zero g1) (mul g3 c4))
    (mul g4 b5)) (mul g5 b6)) (mul g6 d15)
  have h1 : exact result.half1 + exact result.half1 = exact numerator := by
    simpa [result, evaluation, numerator, c4, d15] using half_exact numerator
  have numeratorExact : exact numerator =
      exact g1 + exact g3 * (exact b1 + exact b2 + exact b3 + exact b4) +
      exact g4 * exact b5 + exact g5 * exact b6 +
      exact g6 * (exact b7 + exact b8 + exact b9 + exact b10 + exact b11 +
        exact b12 + exact b13 + exact b14 + exact b15) := by
    simp only [numerator, c4, d15, add_exact, exact_zero, mul_exact]
    ring
  rw [numeratorExact] at h1
  linear_combination 8 * h4 + 4 * h3 + 2 * h2 + h1

#print axioms output_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3Evaluation
