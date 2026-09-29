import V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0Evaluation

/-! # Canonical evaluation certificate for fused chunk one -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1Evaluation

open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1
open V7CallerCurrentReleaseR26GroupedRowsTwiceContributions

abbrev RawQM31 := field.QM31

structure Evaluation
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g2 : CanonicalRaw) : Type where
  coefficientTrace : Chunk1CoefficientTrace
    b0.raw b1.raw b2.raw b3.raw b4.raw b5.raw b6.raw b7.raw
    b8.raw b9.raw b10.raw b11.raw b12.raw b13.raw b14.raw b15.raw
  contributionTrace : Chunk1ContributionTrace groupValues
    coefficientTrace.c15 b7.raw
  half1 : CanonicalRaw
  half2 : CanonicalRaw
  half3 : CanonicalRaw
  half4 : CanonicalRaw
  half1Run : field.QM31.half contributionTrace.sum1 = ok half1.raw
  half2Run : field.QM31.half half1.raw = ok half2.raw
  half3Run : field.QM31.half half2.raw = ok half3.raw
  half4Run : field.QM31.half half3.raw = ok half4.raw

noncomputable def evaluation
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g2 : CanonicalRaw)
    (g1Read : Slice.index_usize groupValues 1#usize = ok g1.raw)
    (g2Read : Slice.index_usize groupValues 2#usize = ok g2.raw) :
    Evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 g1 g2 := by
  let c1 := add b0 b1
  let c2 := add c1 b2
  let c3 := add c2 b3
  let c4 := add c3 b4
  let c5 := add c4 b5
  let c6 := add c5 b6
  let c8 := add c6 b8
  let c9 := add c8 b9
  let c10 := add c9 b10
  let c11 := add c10 b11
  let c12 := add c11 b12
  let c13 := add c12 b13
  let c14 := add c13 b14
  let c15 := add c14 b15
  let coefficientTrace : Chunk1CoefficientTrace
      b0.raw b1.raw b2.raw b3.raw b4.raw b5.raw b6.raw b7.raw
      b8.raw b9.raw b10.raw b11.raw b12.raw b13.raw b14.raw b15.raw := {
    c1 := c1.raw, c2 := c2.raw, c3 := c3.raw, c4 := c4.raw
    c5 := c5.raw, c6 := c6.raw, c8 := c8.raw, c9 := c9.raw
    c10 := c10.raw, c11 := c11.raw, c12 := c12.raw, c13 := c13.raw
    c14 := c14.raw, c15 := c15.raw
    c1Run := add_run b0 b1, c2Run := add_run c1 b2
    c3Run := add_run c2 b3, c4Run := add_run c3 b4
    c5Run := add_run c4 b5, c6Run := add_run c5 b6
    c8Run := add_run c6 b8, c9Run := add_run c8 b9
    c10Run := add_run c9 b10, c11Run := add_run c10 b11
    c12Run := add_run c11 b12, c13Run := add_run c12 b13
    c14Run := add_run c13 b14, c15Run := add_run c14 b15 }
  let product1 := mul g1 c15
  let product2 := mul g2 b7
  let sum0 := add zero product1
  let sum1 := add sum0 product2
  let contributionTrace : Chunk1ContributionTrace groupValues c15.raw b7.raw := {
    value1 := g1.raw, value2 := g2.raw
    product1 := product1.raw, product2 := product2.raw
    sum0 := sum0.raw, sum1 := sum1.raw
    value1Run := g1Read, value2Run := g2Read
    product1Run := mul_run g1 c15, product2Run := mul_run g2 b7
    sum0Run := add_run zero product1, sum1Run := add_run sum0 product2 }
  let half1 := half sum1
  let half2 := half half1
  let half3 := half half2
  let half4 := half half3
  exact {
    coefficientTrace := coefficientTrace
    contributionTrace := contributionTrace
    half1 := half1, half2 := half2, half3 := half3, half4 := half4
    half1Run := half_run sum1, half2Run := half_run half1
    half3Run := half_run half2, half4Run := half_run half3 }

theorem output_exact
    (groupValues : Slice RawQM31)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : CanonicalRaw)
    (g1 g2 : CanonicalRaw)
    (g1Read : Slice.index_usize groupValues 1#usize = ok g1.raw)
    (g2Read : Slice.index_usize groupValues 2#usize = ok g2.raw) :
    let result := evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      b10 b11 b12 b13 b14 b15 g1 g2 g1Read g2Read
    16 * exact result.half4 =
      exact g1 * (exact b0 + exact b1 + exact b2 + exact b3 + exact b4 +
        exact b5 + exact b6 + exact b8 + exact b9 + exact b10 +
        exact b11 + exact b12 + exact b13 + exact b14 + exact b15) +
      exact g2 * exact b7 := by
  dsimp only
  let result := evaluation groupValues b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    b10 b11 b12 b13 b14 b15 g1 g2 g1Read g2Read
  change 16 * exact result.half4 = _
  have h4 : exact result.half4 + exact result.half4 = exact result.half3 := by
    simpa [result, evaluation] using half_exact result.half3
  have h3 : exact result.half3 + exact result.half3 = exact result.half2 := by
    simpa [result, evaluation] using half_exact result.half2
  have h2 : exact result.half2 + exact result.half2 = exact result.half1 := by
    simpa [result, evaluation] using half_exact result.half1
  have h1 : exact result.half1 + exact result.half1 =
      exact (add (add zero (mul g1 (add (add (add (add (add (add (add
        (add (add (add (add (add (add (add b0 b1) b2) b3) b4) b5) b6)
        b8) b9) b10) b11) b12) b13) b14) b15))) (mul g2 b7)) := by
    simpa [result, evaluation] using half_exact
      (add (add zero (mul g1 (add (add (add (add (add (add (add (add
        (add (add (add (add (add (add b0 b1) b2) b3) b4) b5) b6) b8)
        b9) b10) b11) b12) b13) b14) b15))) (mul g2 b7))
  have numeratorExact :
      exact (add (add zero (mul g1 (add (add (add (add (add (add (add
        (add (add (add (add (add (add (add b0 b1) b2) b3) b4) b5) b6)
        b8) b9) b10) b11) b12) b13) b14) b15))) (mul g2 b7)) =
      exact g1 * (exact b0 + exact b1 + exact b2 + exact b3 + exact b4 +
        exact b5 + exact b6 + exact b8 + exact b9 + exact b10 +
        exact b11 + exact b12 + exact b13 + exact b14 + exact b15) +
      exact g2 * exact b7 := by
    simp only [add_exact, exact_zero, mul_exact]
    ring
  rw [numeratorExact] at h1
  linear_combination 8 * h4 + 4 * h3 + 2 * h2 + h1

#print axioms output_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1Evaluation
