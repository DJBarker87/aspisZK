import S5QRaw.GeneratedDotPushConnectionV2
import EbyKPushDotBackend
import EbyKPowerValueCanonicalToPushV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKPushActualRawCoefficientBounds

abbrev PushWide := AspisR1EbyKPushDotBackend.PushWide
abbrev PushQ := AspisR1EbyKPushDotBackend.PushQ
abbrev PushQm := AspisR1EbyKPushDotBackend.PushQm
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev GeneratedQ := AspisR1QRawGeneratedPushConnectionV2.GeneratedQ
abbrev QRaw := AspisR1QRawGeneratedPushConnectionV2.sourceRawFn

abbrev valueLo := AspisR1EbyKPushDotBackend.valueLo
abbrev valueHi := AspisR1EbyKPushDotBackend.valueHi
abbrev scalarQ := AspisR1EbyKPushDotBackend.scalarQ

theorem actual_qraw_matches_generated (a b : PushQ) :
    QRaw a b = QRaw (a : GeneratedQ) (b : GeneratedQ) := by rfl


def qrawCoefficientResult (value : PushWide) (scalar : PushQm) : Prop :=
    ∃ lo hi : Array U64 4#usize,
      QRaw (valueLo value) (scalarQ scalar) = .ok lo ∧
      QRaw (valueHi value) (scalarQ scalar) = .ok hi ∧
      (∃ a b c d e f g h : Nat, ∃ x0 x1 x2 x3 : U64,
        lo = Array.make 4#usize [x0,x1,x2,x3] ∧
        x0.val = AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h ∧
        x1.val = AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h ∧
        x2.val = AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h ∧
        x3.val = AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h ∧
        a = value.c0.c0.a.val ∧ b = value.c0.c0.b.val ∧
        c = value.c0.c1.a.val ∧ d = value.c0.c1.b.val ∧
        e = scalar.c0.a.val ∧ f = scalar.c0.b.val ∧
        g = scalar.c1.a.val ∧ h = scalar.c1.b.val) ∧
      (∃ a b c d e f g h : Nat, ∃ x0 x1 x2 x3 : U64,
        hi = Array.make 4#usize [x0,x1,x2,x3] ∧
        x0.val = AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h ∧
        x1.val = AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h ∧
        x2.val = AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h ∧
        x3.val = AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h ∧
        a = value.c1.c0.a.val ∧ b = value.c1.c0.b.val ∧
        c = value.c1.c1.a.val ∧ d = value.c1.c1.b.val ∧
        e = scalar.c0.a.val ∧ f = scalar.c0.b.val ∧
        g = scalar.c1.a.val ∧ h = scalar.c1.b.val)

 theorem successful_push_qraw_coefficients
    (self : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hv00 : value.c0.c0.a.val ≤ 2^31-2) (hv01 : value.c0.c0.b.val ≤ 2^31-2)
    (hv02 : value.c0.c1.a.val ≤ 2^31-2) (hv03 : value.c0.c1.b.val ≤ 2^31-2)
    (hv10 : value.c1.c0.a.val ≤ 2^31-2) (hv11 : value.c1.c0.b.val ≤ 2^31-2)
    (hv12 : value.c1.c1.a.val ≤ 2^31-2) (hv13 : value.c1.c1.b.val ≤ 2^31-2)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
      .ok (.Ok (),out)) :
    qrawCoefficientResult value scalar := by
  obtain ⟨lo,hi,hlo,hhi,_,_,_,_,hscalar⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend QRaw self value scalar out hrun
  have hva0 : (valueLo value).val[0]!.val ≤ 2^31-2 := by
    simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv00
  have hva1 : (valueLo value).val[1]!.val ≤ 2^31-2 := by
    simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv01
  have hva2 : (valueLo value).val[2]!.val ≤ 2^31-2 := by
    simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv02
  have hva3 : (valueLo value).val[3]!.val ≤ 2^31-2 := by
    simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv03
  have hvb0 : (valueHi value).val[0]!.val ≤ 2^31-2 := by
    simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv10
  have hvb1 : (valueHi value).val[1]!.val ≤ 2^31-2 := by
    simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv11
  have hvb2 : (valueHi value).val[2]!.val ≤ 2^31-2 := by
    simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv12
  have hvb3 : (valueHi value).val[3]!.val ≤ 2^31-2 := by
    simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hv13
  have hs0 : (scalarQ scalar).val[0]!.val ≤ 2^31-2 := by
    have hm : (scalarQ scalar).val[0]! ∈ [scalar.c0.a,scalar.c0.b,scalar.c1.a,scalar.c1.b] := by
      simp [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    have hh := hscalar _ hm
    omega
  have hs1 : (scalarQ scalar).val[1]!.val ≤ 2^31-2 := by
    have hm : (scalarQ scalar).val[1]! ∈ [scalar.c0.a,scalar.c0.b,scalar.c1.a,scalar.c1.b] := by
      simp [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    have hh := hscalar _ hm
    omega
  have hs2 : (scalarQ scalar).val[2]!.val ≤ 2^31-2 := by
    have hm : (scalarQ scalar).val[2]! ∈ [scalar.c0.a,scalar.c0.b,scalar.c1.a,scalar.c1.b] := by
      simp [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    have hh := hscalar _ hm
    omega
  have hs3 : (scalarQ scalar).val[3]!.val ≤ 2^31-2 := by
    have hm : (scalarQ scalar).val[3]! ∈ [scalar.c0.a,scalar.c0.b,scalar.c1.a,scalar.c1.b] := by
      simp [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    have hh := hscalar _ hm
    omega
  have hlow := AspisR1QRawGeneratedPushConnectionV2.source_raw_output_coefficients_v2
    (valueLo value) (scalarQ scalar) lo hlo hva0 hva1 hva2 hva3 hs0 hs1 hs2 hs3
  have hhigh := AspisR1QRawGeneratedPushConnectionV2.source_raw_output_coefficients_v2
    (valueHi value) (scalarQ scalar) hi hhi hvb0 hvb1 hvb2 hvb3 hs0 hs1 hs2 hs3
  rcases hlow with ⟨a,b,c,d,e,f,g,h,x0,x1,x2,x3,hshape,h0,h1,h2,h3,ha,hb,hc',hd,he,hf,hg,hh⟩
  rcases hhigh with ⟨a',b',c',d',e',f',g',h',y0,y1,y2,y3,hshape',h0',h1',h2',h3',ha',hb',hc'',hd',he',hf',hg',hh'⟩
  have hvla : a = value.c0.c0.a.val := by simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using ha
  have hvlb : b = value.c0.c0.b.val := by simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hb
  have hvlc : c = value.c0.c1.a.val := by simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hc'
  have hvld : d = value.c0.c1.b.val := by simpa [valueLo, AspisR1EbyKPushDotBackend.valueLo, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hd
  have hvle : e = scalar.c0.a.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using he
  have hvlf : f = scalar.c0.b.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hf
  have hvlg : g = scalar.c1.a.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hg
  have hvh : h = scalar.c1.b.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hh
  have hvhe : e' = scalar.c0.a.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using he'
  have hvhf : f' = scalar.c0.b.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hf'
  have hvhg : g' = scalar.c1.a.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hg'
  have hvhh : h' = scalar.c1.b.val := by simpa [scalarQ, AspisR1EbyKPushDotBackend.scalarQ, Array.make] using hh'
  have hvha : a' = value.c1.c0.a.val := by simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using ha'
  have hvhb : b' = value.c1.c0.b.val := by simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hb'
  have hvhc : c' = value.c1.c1.a.val := by simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hc''
  have hvhd : d' = value.c1.c1.b.val := by simpa [valueHi, AspisR1EbyKPushDotBackend.valueHi, AspisR1EbyKPushWideToQ.qFromCoords, Array.make] using hd'
  refine ⟨lo,hi,hlo,hhi,?_,?_⟩
  · refine ⟨a,b,c,d,e,f,g,h,x0,x1,x2,x3,hshape,?_,?_,?_,?_,hvla,hvlb,hvlc,hvld,hvle,hvlf,hvlg,hvh⟩
    · simpa [hvla,hvlb,hvlc,hvld,hvle,hvlf,hvlg,hvh] using h0
    · simpa [hvla,hvlb,hvlc,hvld,hvle,hvlf,hvlg,hvh] using h1
    · simpa [hvla,hvlb,hvlc,hvld,hvle,hvlf,hvlg,hvh] using h2
    · simpa [hvla,hvlb,hvlc,hvld,hvle,hvlf,hvlg,hvh] using h3
  · refine ⟨a',b',c',d',e',f',g',h',y0,y1,y2,y3,hshape',?_,?_,?_,?_,hvha,hvhb,hvhc,hvhd,hvhe,hvhf,hvhg,hvhh⟩
    · simpa [hvha,hvhb,hvhc,hvhd,hvle,hvlf,hvlg,hvh] using h0'
    · simpa [hvha,hvhb,hvhc,hvhd,hvle,hvlf,hvlg,hvh] using h1'
    · simpa [hvha,hvhb,hvhc,hvhd,hvle,hvlf,hvlg,hvh] using h2'
    · simpa [hvha,hvhb,hvhc,hvhd,hvle,hvlf,hvlg,hvh] using h3'


theorem successful_push_qraw_coefficients_of_canonical
    (self : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
      .ok (.Ok (),out)) :
    qrawCoefficientResult value scalar := by
  have hb := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds value hcanonical
  exact successful_push_qraw_coefficients self value scalar out
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1
    hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2 hrun

#print axioms actual_qraw_matches_generated
#print axioms successful_push_qraw_coefficients
#print axioms successful_push_qraw_coefficients_of_canonical
end AspisR1EbyKPushActualRawCoefficientBounds
