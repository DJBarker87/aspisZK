import QRawTraceUVBridgeV2
import QRawNoWrapFactsV5
import R22RawQmProductResiduesV15
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1QRawActualC0
open AspisR1CanonicalDotFinish.Proof
open AspisV8R17.RawReducer
abbrev U64 := UScalar UScalarTy.U64

private theorem bind_ok_inv_local {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem mul_success_val (x y z : U64) (h : UScalar.mul x y = .ok z) :
    z.val = x.val*y.val := by
  change UScalar.tryMk UScalarTy.U64 (x.val*y.val) = .ok z at h
  have hspec := UScalar.tryMk_eq UScalarTy.U64 (x.val*y.val)
  rw [h] at hspec
  exact hspec.1

theorem add_val_of_success (x y z : U64)
    (h : lift (core.num.U64.wrapping_add x y) = .ok z)
    (hb : x.val+y.val<2^64) : z.val=x.val+y.val := by
  have hz : U64.wrapping_add x y=z := by
    change Result.ok (U64.wrapping_add x y)=Result.ok z at h
    exact Result.ok.inj h
  rw [← hz, U64.wrapping_add_val_eq]
  simp only [UScalar.size, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt hb

theorem sub_val_of_success (x y z : U64)
    (h : lift (core.num.U64.wrapping_sub x y) = .ok z)
    (hb : y.val≤x.val) : z.val=x.val-y.val := by
  have hz : U64.wrapping_sub x y=z := by
    change Result.ok (U64.wrapping_sub x y)=Result.ok z at h
    exact Result.ok.inj h
  rw [← hz, U64.wrapping_sub_val_eq]
  have hy : y.val<2^64 := y.bv.isLt
  have hx : x.val<2^64 := x.bv.isLt
  have he : x.val+(2^64-y.val)=(x.val-y.val)+2^64 := by omega
  simp only [UScalar.size, UScalarTy.U64_numBits_eq]
  change (x.val+(2^64-y.val))%2^64=x.val-y.val
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem canonicalPP_success_val_local (out : U64)
    (h : canonical.Q.raw.PP=.ok out) : out.val=2147483647*2147483647 := by
  unfold canonical.Q.raw.PP at h
  rcases bind_ok_inv_local h with ⟨x,hx,hrest⟩
  rcases bind_ok_inv_local hrest with ⟨y,hy,hmul⟩
  have hcx : x=UScalar.cast .U64 canonical.P := by
    change Result.ok (UScalar.cast .U64 canonical.P)=.ok x at hx
    exact (Result.ok.inj hx).symm
  have hcy : y=UScalar.cast .U64 canonical.P := by
    change Result.ok (UScalar.cast .U64 canonical.P)=.ok y at hy
    exact (Result.ok.inj hy).symm
  have hp : canonical.P.val=2147483647 := by norm_num [canonical.P,UScalar.ofNatCore_val_eq]
  have hxv : x.val=2147483647 := by
    rw [hcx,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hyv : y.val=2147483647 := by
    rw [hcy,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hout := mul_success_val x y out hmul
  rw [hxv,hyv] at hout
  exact hout

 theorem actual_raw_coefficients (self rhs : AspisR1CanonicalDotFinish.canonical.Q)
    (out : Array U64 4#usize)
    (hraw : AspisR1CanonicalDotFinish.canonical.Q.raw self rhs = .ok out)
    (hguards : AspisR1CanonicalDotFinish.Proof.QRawNoWrapFacts self rhs out)
    : ∃ a b c d e f g h, ∃ out0 out1 out2 out3 : U64,
        out = Array.make 4#usize [out0, out1, out2, out3] ∧
        out0.val = AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h ∧
        out1.val = AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h ∧
        out2.val = AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h ∧
        out3.val = AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h := by
  rcases AspisR1QRawValueBridge.qraw_success_uv self rhs out hraw with
    ⟨v_a, v_a1, v_b, v_c, v_d, v_a2, v_e, v_f, v_g, v_h,
      v_i, v_i1, v_i2, v_i3, v_i4, v_u, v_i5, v_i6, v_i7, v_v,
      v_i8, v_i9, v_i10, v_i11, v_i12, v_i13, v_i14, v_i15, v_i16,
      v_i17, v_i18, v_i19, v_i20, v_i21, v_i22, v_i23, v_i24, v_i25,
      v_i26, v_i27, v_i28, v_i29, v_i30, v_i31, v_i32, v_i33, v_i34,
      v_i35, v_i36, v_i37, v_i38, v_i39, hbody, huval, hvval⟩
  have hguard := hguards v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h v_i v_i1
    v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12 v_i13
    v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24 v_i25
    v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36 v_i37
    v_i38 v_i39 hbody
  rcases hguard with ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18⟩
  rcases hbody with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,
    h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  have w1 := add_val_of_success v_i v_i1 v_i2 h13 g1
  have w2 := sub_val_of_success v_i2 v_i3 v_i4 h15 g2
  have w3 := add_val_of_success v_i5 v_i6 v_i7 h19 g3
  have w4 := add_val_of_success v_i8 v_i1 v_i9 h22 g4
  have w5 := sub_val_of_success v_i9 v_i10 v_i11 h24 g5
  have w6 := add_val_of_success v_i11 v_i12 v_i13 h26 g6
  have w7 := add_val_of_success v_i13 v_i15 v_i16 h29 g7
  have w8 := sub_val_of_success v_i16 v_v v_i17 h30 g8
  have w9 := add_val_of_success v_i18 v_i19 v_i20 h33 g9
  have w10 := add_val_of_success v_i20 v_u v_i21 h34 g10
  have w11 := add_val_of_success v_i21 v_i22 v_i23 h36 g11
  have w12 := add_val_of_success v_i24 v_i25 v_i26 h39 g12
  have w13 := add_val_of_success v_i26 v_i27 v_i28 h41 g13
  have w14 := sub_val_of_success v_i28 v_i29 v_i30 h43 g14
  have w15 := sub_val_of_success v_i30 v_i31 v_i32 h45 g15
  have w16 := add_val_of_success v_i33 v_i34 v_i35 h48 g16
  have w17 := add_val_of_success v_i35 v_i36 v_i37 h50 g17
  have w18 := add_val_of_success v_i37 v_i38 v_i39 h52 g18
  have hmulCg := mul_success_val v_c v_g v_i h11
  have hmulDh := mul_success_val v_d v_h v_i3 h14
  have hmulCh := mul_success_val v_c v_h v_i5 h17
  have hmulDg := mul_success_val v_d v_g v_i6 h18
  have hmulAe := mul_success_val v_a1 v_e v_i8 h21
  have hmulBf := mul_success_val v_b v_f v_i10 h23
  have hmulAf := mul_success_val v_a1 v_f v_i18 h31
  have hmulBe := mul_success_val v_b v_e v_i19 h32
  have hmulTwoV0 := mul_success_val (2#u64) v_v v_i22 h35
  have hmulTwoV : v_i22.val = 2*v_v.val := by simpa using hmulTwoV0
  have hmulAg := mul_success_val v_a1 v_g v_i24 h37
  have hmulCe := mul_success_val v_c v_e v_i25 h38
  have hmulTwoPP0 := mul_success_val (2#u64) v_i1 v_i27 h40
  have hmulTwoPP : v_i27.val = 2*v_i1.val := by simpa using hmulTwoPP0
  have hmulBh := mul_success_val v_b v_h v_i29 h42
  have hmulDf := mul_success_val v_d v_f v_i31 h44
  have hmulAh := mul_success_val v_a1 v_h v_i33 h46
  have hmulBg := mul_success_val v_b v_g v_i34 h47
  have hmulCf := mul_success_val v_c v_f v_i36 h49
  have hmulDe := mul_success_val v_d v_e v_i38 h51
  have hmulTwoU0 := mul_success_val (2#u64) v_u v_i12 h25
  have hmulTwoU : v_i12.val = 2*v_u.val := by simpa using hmulTwoU0
  have hpp0 := canonicalPP_success_val_local v_i1 h12
  have hpp : v_i1.val = P*P := by simpa [P] using hpp0
  have hcastP : v_i14.val = P := by
    change Result.ok (core.convert.num.FromU64U32.from AspisR1CanonicalDotFinish.canonical.P) = .ok v_i14 at h27
    have hcast : core.convert.num.FromU64U32.from AspisR1CanonicalDotFinish.canonical.P = v_i14 :=
      Result.ok.inj h27
    rw [← hcast, qRawMask64_val]
  have hthreeP0 := mul_success_val (3#u64) v_i14 v_i15 h28
  have hthreeP : v_i15.val = 3*v_i14.val := by simpa using hthreeP0
  have hi4 : v_i4.val = v_c.val*v_g.val + P*P - v_d.val*v_h.val := by
    calc
      v_i4.val = v_i2.val-v_i3.val := w2
      _ = (v_i.val+v_i1.val)-v_i3.val := by rw [w1]
      _ = v_c.val*v_g.val + P*P - v_d.val*v_h.val := by rw [hmulCg, hpp, hmulDh]
  have hi7 : v_i7.val = v_c.val*v_h.val + v_d.val*v_g.val := by
    calc
      v_i7.val = v_i5.val+v_i6.val := w3
      _ = v_c.val*v_h.val + v_d.val*v_g.val := by rw [hmulCh, hmulDg]
  have hrawU : AspisR1.R22RawQmProductResidues.rawU v_c.val v_d.val v_g.val v_h.val = v_u.val := by
    unfold AspisR1.R22RawQmProductResidues.rawU
    rw [← hi4, huval]
  have hrawV : AspisR1.R22RawQmProductResidues.rawV v_c.val v_d.val v_g.val v_h.val = v_v.val := by
    unfold AspisR1.R22RawQmProductResidues.rawV
    rw [← hi7, hvval]
  have hc0 : v_i17.val = AspisR1.R22RawQmProductResidues.rawC0
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC0
    rw [w8,w7,w6,w5,w4]
    rw [hmulAe, hpp, hmulBf, hmulTwoU, hthreeP, hcastP, hrawU, hrawV]
    omega
  have hc1 : v_i23.val = AspisR1.R22RawQmProductResidues.rawC1
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC1
    rw [w11,w10,w9,hmulAf,hmulBe,hmulTwoV,hrawU,hrawV]
    omega
  have hc2 : v_i32.val = AspisR1.R22RawQmProductResidues.rawC2
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC2
    rw [w15,w14,w13,w12,hmulAg,hmulCe,hmulTwoPP,hpp,hmulBh,hmulDf]
    omega
  have hc3 : v_i39.val = AspisR1.R22RawQmProductResidues.rawC3
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC3
    rw [w18,w17,w16,hmulAh,hmulBg,hmulCf,hmulDe]
    omega
  have hout := h53
  exact ⟨v_a1.val, v_b.val, v_c.val, v_d.val, v_e.val, v_f.val, v_g.val,
    v_h.val, v_i17, v_i23, v_i32, v_i39, hout, hc0, hc1, hc2, hc3⟩
#print axioms actual_raw_coefficients
end AspisR1QRawActualC0
