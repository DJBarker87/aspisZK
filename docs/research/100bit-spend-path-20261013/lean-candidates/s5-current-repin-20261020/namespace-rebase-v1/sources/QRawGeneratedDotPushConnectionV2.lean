import S5QRaw.ActualCoefficientsFromBoundsV2
import AspisR1EbyKDotPushSourceV1.LoopAdapter
import OriginalDotPushRawLoopToLiteralV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1QRawGeneratedPushConnectionV2

abbrev GeneratedQ := AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Q
abbrev ActualQ := AspisR1CanonicalQRawUnified.canonical.Q
abbrev Dot := AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot

def sourceRawFn (a b : GeneratedQ) : Result (Array U64 4#usize) :=
  AspisR1CanonicalQRawUnified.canonical.Q.raw a b

 theorem source_raw_output_coefficients_v2
    (a b : GeneratedQ) (out : Array U64 4#usize)
    (hraw : sourceRawFn a b = .ok out)
    (ha0 : a.val[0]!.val ≤ 2^31-2) (ha1 : a.val[1]!.val ≤ 2^31-2)
    (ha2 : a.val[2]!.val ≤ 2^31-2) (ha3 : a.val[3]!.val ≤ 2^31-2)
    (hb0 : b.val[0]!.val ≤ 2^31-2) (hb1 : b.val[1]!.val ≤ 2^31-2)
    (hb2 : b.val[2]!.val ≤ 2^31-2) (hb3 : b.val[3]!.val ≤ 2^31-2) :
    ∃ na nb nc nd ne nf ng nh : Nat, ∃ x0 x1 x2 x3 : U64,
      out = Array.make 4#usize [x0,x1,x2,x3] ∧
      x0.val = AspisR1.R22RawQmProductResidues.rawC0 na nb nc nd ne nf ng nh ∧
      x1.val = AspisR1.R22RawQmProductResidues.rawC1 na nb nc nd ne nf ng nh ∧
      x2.val = AspisR1.R22RawQmProductResidues.rawC2 na nb nc nd ne nf ng nh ∧
      x3.val = AspisR1.R22RawQmProductResidues.rawC3 na nb nc nd ne nf ng nh ∧
      na = a.val[0]!.val ∧ nb = a.val[1]!.val ∧ nc = a.val[2]!.val ∧ nd = a.val[3]!.val ∧
      ne = b.val[0]!.val ∧ nf = b.val[1]!.val ∧ ng = b.val[2]!.val ∧ nh = b.val[3]!.val := by
  have hraw' : AspisR1CanonicalQRawUnified.canonical.Q.raw a b = .ok out := hraw
  have ha0' : a.val[0]!.val ≤ 2^31-2 := ha0
  have ha1' : a.val[1]!.val ≤ 2^31-2 := ha1
  have ha2' : a.val[2]!.val ≤ 2^31-2 := ha2
  have ha3' : a.val[3]!.val ≤ 2^31-2 := ha3
  have hb0' : b.val[0]!.val ≤ 2^31-2 := hb0
  have hb1' : b.val[1]!.val ≤ 2^31-2 := hb1
  have hb2' : b.val[2]!.val ≤ 2^31-2 := hb2
  have hb3' : b.val[3]!.val ≤ 2^31-2 := hb3
  exact AspisR1QRawActualC0V2.actual_raw_coefficients_of_input_bounds_v2 a b out hraw'
    ha0' ha1' ha2' ha3' hb0' hb1' hb2' hb3' 

theorem generated_push_success_from_source_qraw_v2
    (a b : GeneratedQ) (out : Array U64 4#usize)
    (s0 s1 s2 s3 : U64)
    (ha0 : a.val[0]!.val ≤ 2^31-2) (ha1 : a.val[1]!.val ≤ 2^31-2)
    (ha2 : a.val[2]!.val ≤ 2^31-2) (ha3 : a.val[3]!.val ≤ 2^31-2)
    (hb0 : b.val[0]!.val ≤ 2^31-2) (hb1 : b.val[1]!.val ≤ 2^31-2)
    (hb2 : b.val[2]!.val ≤ 2^31-2) (hb3 : b.val[3]!.val ≤ 2^31-2)
    (hraw : sourceRawFn a b = .ok out) :
    ∃ na nb nc nd ne nf ng nh : Nat, ∃ r0 r1 r2 r3 : U64,
      out = Array.make 4#usize [r0,r1,r2,r3] ∧
      r0.val = AspisR1.R22RawQmProductResidues.rawC0 na nb nc nd ne nf ng nh ∧
      r1.val = AspisR1.R22RawQmProductResidues.rawC1 na nb nc nd ne nf ng nh ∧
      r2.val = AspisR1.R22RawQmProductResidues.rawC2 na nb nc nd ne nf ng nh ∧
      r3.val = AspisR1.R22RawQmProductResidues.rawC3 na nb nc nd ne nf ng nh ∧
      na = a.val[0]!.val ∧ nb = a.val[1]!.val ∧ nc = a.val[2]!.val ∧ nd = a.val[3]!.val ∧
      ne = b.val[0]!.val ∧ nf = b.val[1]!.val ∧ ng = b.val[2]!.val ∧ nh = b.val[3]!.val ∧
      AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot.push_raw sourceRawFn
        ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b =
        .ok ⟨Array.make 4#usize
          [AspisR1DotPushLocal.Proof.updateWord s0 r0,
           AspisR1DotPushLocal.Proof.updateWord s1 r1,
           AspisR1DotPushLocal.Proof.updateWord s2 r2,
           AspisR1DotPushLocal.Proof.updateWord s3 r3]⟩ := by
  obtain ⟨na,nb,nc,nd,ne,nf,ng,nh,r0,r1,r2,r3, hshape, h0,h1,h2,h3,
    hna,hnb,hnc,hnd,hne,hnf,hng,hnh⟩ :=
    source_raw_output_coefficients_v2 a b out hraw ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have hrawExact : sourceRawFn a b = .ok (Array.make 4#usize [r0,r1,r2,r3]) := by
    have hh := hraw
    rw [hshape] at hh
    exact hh
  refine ⟨na, ?_⟩
  refine ⟨nb, ?_⟩
  refine ⟨nc, ?_⟩
  refine ⟨nd, ?_⟩
  refine ⟨ne, ?_⟩
  refine ⟨nf, ?_⟩
  refine ⟨ng, ?_⟩
  refine ⟨nh, ?_⟩
  refine ⟨r0, ?_⟩
  refine ⟨r1, ?_⟩
  refine ⟨r2, ?_⟩
  refine ⟨r3, ?_⟩
  refine ⟨hshape, h0, h1, h2, h3, hna, hnb, hnc, hnd, hne, hnf, hng, hnh, ?_⟩
  simpa [sourceRawFn, Dot] using
    (AspisR1DotPushOriginalRaw.Proof.push_raw_success sourceRawFn a b
      s0 s1 s2 s3 r0 r1 r2 r3 hrawExact)

#print axioms source_raw_output_coefficients_v2
#print axioms generated_push_success_from_source_qraw_v2
end AspisR1QRawGeneratedPushConnectionV2
