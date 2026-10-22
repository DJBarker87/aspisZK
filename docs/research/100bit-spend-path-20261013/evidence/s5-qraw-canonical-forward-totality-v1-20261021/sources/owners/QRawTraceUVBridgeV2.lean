import S5QRaw.SuccessTracePropV4
import S5QRaw.NoWrapFactsV5
import S5QRaw.PartialFoldBridgeV7
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1QRawValueBridge
open AspisR1CanonicalQRawUnified.Proof
abbrev U64 := UScalar UScalarTy.U64

def QRawTraceWithUV (self rhs : AspisR1CanonicalQRawUnified.canonical.Q) (out : Array U64 4#usize) : Prop :=
  ∃ (v_a : Array U64 4#usize) (v_a1 v_b v_c v_d : U64)
    (v_a2 : Array U64 4#usize) (v_e v_f v_g v_h : U64)
    (v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11
      v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23
      v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35
      v_i36 v_i37 v_i38 v_i39 : U64),
    QRawTraceBody self rhs out v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h
      v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12
      v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24
      v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36
      v_i37 v_i38 v_i39 ∧ v_u.val = AspisV8R17.RawReducer.foldBits v_i4.val ∧
      v_v.val = AspisV8R17.RawReducer.foldBits v_i7.val

theorem qraw_success_uv (self rhs : AspisR1CanonicalQRawUnified.canonical.Q) (out : Array U64 4#usize)
    (hraw : AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs = .ok out) : QRawTraceWithUV self rhs out := by
  rcases qraw_success_trace self rhs out hraw with
    ⟨v_a, v_a1, v_b, v_c, v_d, v_a2, v_e, v_f, v_g, v_h, v_i, v_i1, v_i2, v_i3, v_i4, v_u, v_i5, v_i6, v_i7, v_v, v_i8, v_i9, v_i10, v_i11, v_i12, v_i13, v_i14, v_i15, v_i16, v_i17, v_i18, v_i19, v_i20, v_i21, v_i22, v_i23, v_i24, v_i25, v_i26, v_i27, v_i28, v_i29, v_i30, v_i31, v_i32, v_i33, v_i34, v_i35, v_i36, v_i37, v_i38, v_i39, hbody⟩
  let hbody0 := hbody
  rcases hbody with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53⟩
  obtain ⟨u0, hu0, huval⟩ := AspisR1CanonicalQRawUnified.Proof.qRawPartial_success v_i4
  have hequ : v_u = u0 := Result.ok.inj (h16.symm.trans hu0)
  have hvu : v_u.val = AspisV8R17.RawReducer.foldBits v_i4.val := by rw [hequ, huval]
  obtain ⟨v0, hv0, hvval⟩ := AspisR1CanonicalQRawUnified.Proof.qRawPartial_success v_i7
  have heqv : v_v = v0 := Result.ok.inj (h20.symm.trans hv0)
  have hvv : v_v.val = AspisV8R17.RawReducer.foldBits v_i7.val := by rw [heqv, hvval]
  exact ⟨v_a, v_a1, v_b, v_c, v_d, v_a2, v_e, v_f, v_g, v_h, v_i, v_i1, v_i2, v_i3, v_i4, v_u, v_i5, v_i6, v_i7, v_v, v_i8, v_i9, v_i10, v_i11, v_i12, v_i13, v_i14, v_i15, v_i16, v_i17, v_i18, v_i19, v_i20, v_i21, v_i22, v_i23, v_i24, v_i25, v_i26, v_i27, v_i28, v_i29, v_i30, v_i31, v_i32, v_i33, v_i34, v_i35, v_i36, v_i37, v_i38, v_i39, hbody0, hvu, hvv⟩
#print axioms qraw_success_uv
end AspisR1QRawValueBridge
