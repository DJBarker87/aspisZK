import QRawNoWrapFactsV5
import QRawPartialFoldBridgeV7
import R22RawQmProductResiduesV15
import R22FastPairingRawRanges
import S5CanonicalProductRangesV1
import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5CurrentRepin
open AspisR1CanonicalDotFinish.Proof
open AspisV8R17.RawReducer
abbrev U64 := UScalar UScalarTy.U64

private theorem rawFold_eq_batchedFold (n : Nat) :
    AspisV8R17.RawReducer.foldBits n = AspisR1BatchedFoldArithmetic.fold n := by
  rw [AspisV8R17.RawReducer.foldBits_eq_fold31]
  rfl

private theorem bind_ok_inv_local {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem mul_success_val (x y z : U64) (h : UScalar.mul x y = .ok z) :
    z.val = x.val*y.val := by
  change UScalar.tryMk UScalarTy.U64 (x.val*y.val) = .ok z at h
  have hspec := UScalar.tryMk_eq UScalarTy.U64 (x.val*y.val)
  rw [h] at hspec
  exact hspec.1

private theorem add_val_of_success (x y z : U64)
    (h : lift (core.num.U64.wrapping_add x y) = .ok z)
    (hb : x.val+y.val<2^64) : z.val=x.val+y.val := by
  have hz : U64.wrapping_add x y=z := by
    change Result.ok (U64.wrapping_add x y)=Result.ok z at h
    exact Result.ok.inj h
  rw [← hz, U64.wrapping_add_val_eq]
  simp only [UScalar.size, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt hb

private theorem sub_val_of_success (x y z : U64)
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

private theorem canonicalPP_success_val (out : U64)
    (h : AspisR1CanonicalDotFinish.canonical.Q.raw.PP=.ok out) :
    out.val=2147483647*2147483647 := by
  unfold AspisR1CanonicalDotFinish.canonical.Q.raw.PP at h
  rcases bind_ok_inv_local h with ⟨x,hx,hrest⟩
  rcases bind_ok_inv_local hrest with ⟨y,hy,hmul⟩
  have hcx : x=UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P := by
    change Result.ok (UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P)=.ok x at hx
    exact (Result.ok.inj hx).symm
  have hcy : y=UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P := by
    change Result.ok (UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P)=.ok y at hy
    exact (Result.ok.inj hy).symm
  have hp : AspisR1CanonicalDotFinish.canonical.P.val=2147483647 := by
    norm_num [AspisR1CanonicalDotFinish.canonical.P,UScalar.ofNatCore_val_eq]
  have hxv : x.val=2147483647 := by
    rw [hcx,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hyv : y.val=2147483647 := by
    rw [hcy,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hout := mul_success_val x y out hmul
  rw [hxv,hyv] at hout
  exact hout

/-- Actual emitted Q.raw trace plus canonical input-limb bounds implies every
sequential U64 wrap guard required by the source-shaped no-wrap interface.
The products and intermediate operands are the trace witnesses themselves;
only their limb bounds are supplied. -/
theorem trace_no_wrap_of_canonical_limbs
    (self rhs : AspisR1CanonicalDotFinish.canonical.Q) (out : Array U64 4#usize)
    (v_a : Array U64 4#usize) (v_a1 v_b v_c v_d : U64)
    (v_a2 : Array U64 4#usize) (v_e v_f v_g v_h : U64)
    (v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11
      v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23
      v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35
      v_i36 v_i37 v_i38 v_i39 : U64)
    (ha : v_a1.val ≤ 2^31-2) (hb : v_b.val ≤ 2^31-2)
    (hc : v_c.val ≤ 2^31-2) (hd : v_d.val ≤ 2^31-2)
    (he : v_e.val ≤ 2^31-2) (hf : v_f.val ≤ 2^31-2)
    (hg : v_g.val ≤ 2^31-2) (hh : v_h.val ≤ 2^31-2)
    (hbody : QRawTraceBody self rhs out v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h
      v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12
      v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24
      v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36
      v_i37 v_i38 v_i39) :
    v_i.val + v_i1.val < 2^64 ∧ v_i3.val ≤ v_i2.val ∧ v_i5.val + v_i6.val < 2^64 ∧
    v_i8.val + v_i1.val < 2^64 ∧ v_i10.val ≤ v_i9.val ∧ v_i11.val + v_i12.val < 2^64 ∧
    v_i13.val + v_i15.val < 2^64 ∧ v_v.val ≤ v_i16.val ∧
    v_i18.val + v_i19.val < 2^64 ∧ v_i20.val + v_u.val < 2^64 ∧
    v_i21.val + v_i22.val < 2^64 ∧ v_i24.val + v_i25.val < 2^64 ∧
    v_i26.val + v_i27.val < 2^64 ∧ v_i29.val ≤ v_i28.val ∧ v_i31.val ≤ v_i30.val ∧
    v_i33.val + v_i34.val < 2^64 ∧ v_i35.val + v_i36.val < 2^64 ∧
    v_i37.val + v_i38.val < 2^64 := by
  rcases hbody with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,
    h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  have hc_g := mul_success_val v_c v_g v_i h11
  have hd_h := mul_success_val v_d v_h v_i3 h14
  have hc_h := mul_success_val v_c v_h v_i5 h17
  have hd_g := mul_success_val v_d v_g v_i6 h18
  have ha_e := mul_success_val v_a1 v_e v_i8 h21
  have hb_f := mul_success_val v_b v_f v_i10 h23
  have ha_f := mul_success_val v_a1 v_f v_i18 h31
  have hb_e := mul_success_val v_b v_e v_i19 h32
  have ha_g := mul_success_val v_a1 v_g v_i24 h37
  have hc_e := mul_success_val v_c v_e v_i25 h38
  have hb_h := mul_success_val v_b v_h v_i29 h42
  have hd_f := mul_success_val v_d v_f v_i31 h44
  have ha_h := mul_success_val v_a1 v_h v_i33 h46
  have hb_g := mul_success_val v_b v_g v_i34 h47
  have hc_f := mul_success_val v_c v_f v_i36 h49
  have hd_e := mul_success_val v_d v_e v_i38 h51
  have hpp0 := canonicalPP_success_val v_i1 h12
  have hpp : v_i1.val=(2^31-1)^2 := by simpa using hpp0
  have hprod := canonical_product_bound v_a1.val v_b.val v_c.val v_d.val
    v_e.val v_f.val v_g.val v_h.val ha hb hc hd he hf hg hh
  have hr := AspisR1.R22FastPairingRawRanges.raw_ranges
    (v_a1.val*v_e.val) (v_b.val*v_f.val) (v_c.val*v_g.val) (v_d.val*v_h.val)
    (v_c.val*v_h.val) (v_d.val*v_g.val) (v_a1.val*v_f.val) (v_b.val*v_e.val)
    (v_a1.val*v_g.val) (v_c.val*v_e.val) (v_b.val*v_h.val) (v_d.val*v_f.val)
    (v_a1.val*v_h.val) (v_b.val*v_g.val) (v_c.val*v_f.val) (v_d.val*v_e.val) hprod
  dsimp only at hr
  rcases hr with ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20⟩
  have g1 : v_i.val+v_i1.val<2^64 := by simpa [hc_g,hpp] using r1
  have w1 := add_val_of_success v_i v_i1 v_i2 h13 g1
  have g2 : v_i3.val≤v_i2.val := by simpa [hd_h,w1,hc_g,hpp] using r2
  have w2 := sub_val_of_success v_i2 v_i3 v_i4 h15 g2
  have g3 : v_i5.val+v_i6.val<2^64 := by simpa [hc_h,hd_g] using r3
  have w3 := add_val_of_success v_i5 v_i6 v_i7 h19 g3
  have hu : v_u.val=AspisV8R17.RawReducer.foldBits v_i4.val := by
    obtain ⟨u0,hu0,huval⟩ := qRawPartial_success v_i4
    have heq : v_u=u0 := Result.ok.inj (h16.symm.trans hu0)
    rw [heq,huval]
  have hinputU : v_i4.val=v_c.val*v_g.val+(2^31-1)^2-v_d.val*v_h.val := by
    calc v_i4.val=v_i2.val-v_i3.val := w2
      _ = (v_i.val+v_i1.val)-v_i3.val := by rw [w1]
      _ = v_c.val*v_g.val+(2^31-1)^2-v_d.val*v_h.val := by rw [hc_g,hpp,hd_h]
  have hrawU : AspisV8R17.RawReducer.foldBits
      (v_c.val*v_g.val+(2^31-1)^2-v_d.val*v_h.val)=v_u.val := by
    unfold AspisR1.R22RawQmProductResidues.rawU at *
    rw [← hinputU, hu]
  have hbatchedU : AspisR1BatchedFoldArithmetic.fold
      (v_c.val*v_g.val+(2^31-1)^2-v_d.val*v_h.val)=v_u.val := by
    rw [← rawFold_eq_batchedFold, hrawU]
  have hfoldInputU : AspisV8R17.RawReducer.foldBits v_i4.val =
      AspisR1BatchedFoldArithmetic.fold
        (v_c.val*v_g.val+(2^31-1)^2-v_d.val*v_h.val) := by
    rw [hinputU, rawFold_eq_batchedFold]
  have g4 : v_i8.val+v_i1.val<2^64 := by simpa [ha_e,hpp] using r4
  have w4 := add_val_of_success v_i8 v_i1 v_i9 h22 g4
  have g5 : v_i10.val≤v_i9.val := by simpa [hb_f,w4,ha_e,hpp] using r5
  have w5 := sub_val_of_success v_i9 v_i10 v_i11 h24 g5
  have hmulTwoU0 := mul_success_val (2#u64) v_u v_i12 h25
  have hmulTwoU : v_i12.val=2*v_u.val := by simpa using hmulTwoU0
  have g6 : v_i11.val+v_i12.val<2^64 := by
    simpa [w4,w5,ha_e,hpp,hb_f,hmulTwoU,hu,hrawU,hbatchedU,hfoldInputU] using r6
  have w6 := add_val_of_success v_i11 v_i12 v_i13 h26 g6
  have hcastP : v_i14.val = P := by
    change Result.ok (core.convert.num.FromU64U32.from AspisR1CanonicalDotFinish.canonical.P) = .ok v_i14 at h27
    have hcast : core.convert.num.FromU64U32.from AspisR1CanonicalDotFinish.canonical.P = v_i14 :=
      Result.ok.inj h27
    rw [← hcast]
    exact qRawMask64_val
  have hmulThreeP0 := mul_success_val (3#u64) v_i14 v_i15 h28
  have hthreeP : v_i15.val=3*P := by simpa [hcastP] using hmulThreeP0
  have g7 : v_i13.val+v_i15.val<2^64 := by
    rw [← hfoldInputU] at r7
    simpa [w6,w4,w5,ha_e,hpp,hb_f,hmulTwoU,hu,hrawU,hthreeP,P] using r7
  have w7 := add_val_of_success v_i13 v_i15 v_i16 h29 g7
  have hv : v_v.val=AspisV8R17.RawReducer.foldBits v_i7.val := by
    obtain ⟨v0,hv0,hvval⟩ := qRawPartial_success v_i7
    have heq : v_v=v0 := Result.ok.inj (h20.symm.trans hv0)
    rw [heq,hvval]
  have hinputV : v_i7.val=v_c.val*v_h.val+v_d.val*v_g.val := by
    calc v_i7.val=v_i5.val+v_i6.val := w3
      _ = v_c.val*v_h.val+v_d.val*v_g.val := by rw [hc_h,hd_g]
  have hrawV : AspisV8R17.RawReducer.foldBits
      (v_c.val*v_h.val+v_d.val*v_g.val)=v_v.val := by
    unfold AspisR1.R22RawQmProductResidues.rawV at *
    rw [← hinputV,hv]
  have hbatchedV : AspisR1BatchedFoldArithmetic.fold
      (v_c.val*v_h.val+v_d.val*v_g.val)=v_v.val := by
    rw [← rawFold_eq_batchedFold, hrawV]
  have g8 : v_v.val≤v_i16.val := by
    rw [← hfoldInputU] at r8
    simpa [w7,w6,w5,w4,ha_e,hpp,hb_f,hmulTwoU,hu,hrawU,hthreeP,P,hrawV,hbatchedV] using r8
  have g9 : v_i18.val+v_i19.val<2^64 := by simpa [ha_f,hb_e] using r9
  have w9 := add_val_of_success v_i18 v_i19 v_i20 h33 g9
  have g10 : v_i20.val+v_u.val<2^64 := by
    rw [← hbatchedU]
    simpa [w9,ha_f,hb_e] using r10
  have w10 := add_val_of_success v_i20 v_u v_i21 h34 g10
  have hmulTwoV0 := mul_success_val (2#u64) v_v v_i22 h35
  have hmulTwoV : v_i22.val=2*v_v.val := by simpa using hmulTwoV0
  have g11 : v_i21.val+v_i22.val<2^64 := by
    rw [hbatchedU] at r11
    simpa [w10,w9,ha_f,hb_e,hmulTwoV,hrawV,hbatchedV] using r11
  have g12 : v_i24.val+v_i25.val<2^64 := by simpa [ha_g,hc_e] using r12
  have w12 := add_val_of_success v_i24 v_i25 v_i26 h39 g12
  have hmulTwoPP0 := mul_success_val (2#u64) v_i1 v_i27 h40
  have hmulTwoPP : v_i27.val=2*((2^31-1)^2) := by simpa [hpp] using hmulTwoPP0
  have g13 : v_i26.val+v_i27.val<2^64 := by simpa [w12,ha_g,hc_e,hmulTwoPP] using r13
  have w13 := add_val_of_success v_i26 v_i27 v_i28 h41 g13
  have g14 : v_i29.val≤v_i28.val := by simpa [hb_h,w13,w12,ha_g,hc_e,hmulTwoPP] using r14
  have w14 := sub_val_of_success v_i28 v_i29 v_i30 h43 g14
  have g15 : v_i31.val≤v_i30.val := by simpa [hd_f,w14,w13,w12,ha_g,hc_e,hmulTwoPP,hb_h] using r15
  have g16 : v_i33.val+v_i34.val<2^64 := by simpa [ha_h,hb_g] using r16
  have w16 := add_val_of_success v_i33 v_i34 v_i35 h48 g16
  have g17 : v_i35.val+v_i36.val<2^64 := by simpa [w16,hc_f,ha_h,hb_g] using r17
  have w17 := add_val_of_success v_i35 v_i36 v_i37 h50 g17
  have g18 : v_i37.val+v_i38.val<2^64 := by simpa [w17,hd_e,w16,hc_f,ha_h,hb_g] using r18
  exact ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18⟩

#print axioms trace_no_wrap_of_canonical_limbs
end AspisR1S5CurrentRepin
