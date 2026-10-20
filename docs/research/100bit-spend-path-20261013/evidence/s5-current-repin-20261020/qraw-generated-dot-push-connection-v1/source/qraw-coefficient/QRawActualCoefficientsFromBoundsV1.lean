import QRawTraceUVBridgeV2
import SelectorArrayMapSuccess
import QRawNoWrapFromCanonicalTraceV1
import QRawNoWrapFactsV5
import R22RawQmProductResiduesV15
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1QRawActualC0
open AspisR1CanonicalDotFinish.Proof
open AspisV8R17.RawReducer
abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := UScalar UScalarTy.U32
open AspisV8R19.TraversalRuntime

private theorem from32_val_local (x : U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  exact BitVec.toNat_setWidth_of_le (by decide)

private theorem mapState_closure_zero_local (xs : List U32) :
    mapState AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapState]
    have hx : AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
        () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
      simp [AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
        core.convert.num.FromU64U32.from, lift]
    rw [hx]
    simp only [bind_tc_ok]
    rw [ih]
    rfl

private theorem mapState_closure_one_local (xs : List U32) :
    mapState AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapState]
    have hx : AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
        () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
      simp [AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
        core.convert.num.FromU64U32.from, lift]
    rw [hx]
    simp only [bind_tc_ok]
    rw [ih]
    rfl

theorem closure_zero_map_val_local (x : Array U32 4#usize) (y : Array U64 4#usize)
    (h : core.array.Array.map
      AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 x () = .ok y) :
    y.val = x.val.map core.convert.num.FromU64U32.from := by
  have hs := Aeneas.Std.core.array.Array.map_success
    AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 x ()
    (x.val.map core.convert.num.FromU64U32.from) () (mapState_closure_zero_local x.val)
  have heq : y = ⟨x.val.map core.convert.num.FromU64U32.from,
      (AspisV8R19.TraversalRuntime.mapState_length _ _ _ _ _
        (mapState_closure_zero_local x.val)).trans x.property⟩ := Result.ok.inj (h.symm.trans hs)
  exact congrArg (fun z : Array U64 4#usize => z.val) heq

theorem closure_one_map_val_local (x : Array U32 4#usize) (y : Array U64 4#usize)
    (h : core.array.Array.map
      AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 x () = .ok y) :
    y.val = x.val.map core.convert.num.FromU64U32.from := by
  have hs := Aeneas.Std.core.array.Array.map_success
    AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 x ()
    (x.val.map core.convert.num.FromU64U32.from) () (mapState_closure_one_local x.val)
  have heq : y = ⟨x.val.map core.convert.num.FromU64U32.from,
      (AspisV8R19.TraversalRuntime.mapState_length _ _ _ _ _
        (mapState_closure_one_local x.val)).trans x.property⟩ := Result.ok.inj (h.symm.trans hs)
  exact congrArg (fun z : Array U64 4#usize => z.val) heq

theorem array_index_usize_ok_local {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem map_index_eq_local {n : Usize}
    (a : Array U32 n) (mapped : Array U64 n) (i : Usize)
    (hi : i.val < n.val) (hmap : mapped.val = a.val.map core.convert.num.FromU64U32.from)
    (x : U64) (hread : Array.index_usize mapped i = .ok x) :
    x.val = (a.val[i.val]'(by simpa [a.property] using hi)).val := by
  have hspec := array_index_usize_ok_local mapped i hi
  have hv : mapped.val[i.val]'(by simpa [mapped.property] using hi) =
      core.convert.num.FromU64U32.from (a.val[i.val]'(by simpa [a.property] using hi)) := by
    simpa only [hmap, List.getElem_map]
  have hidx : x = mapped.val[i.val]'(by simpa [mapped.property] using hi) :=
    Result.ok.inj (hread.symm.trans hspec)
  rw [hidx,hv,from32_val_local]

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
    (h : AspisR1CanonicalDotFinish.canonical.Q.raw.PP=.ok out) : out.val=2147483647*2147483647 := by
  unfold AspisR1CanonicalDotFinish.canonical.Q.raw.PP at h
  rcases bind_ok_inv_local h with ⟨x,hx,hrest⟩
  rcases bind_ok_inv_local hrest with ⟨y,hy,hmul⟩
  have hcx : x=UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P := by
    change Result.ok (UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P)=.ok x at hx
    exact (Result.ok.inj hx).symm
  have hcy : y=UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P := by
    change Result.ok (UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P)=.ok y at hy
    exact (Result.ok.inj hy).symm
  have hp : AspisR1CanonicalDotFinish.canonical.P.val=2147483647 := by norm_num [AspisR1CanonicalDotFinish.canonical.P,UScalar.ofNatCore_val_eq]
  have hxv : x.val=2147483647 := by
    rw [hcx,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hyv : y.val=2147483647 := by
    rw [hcy,UScalar.cast_val_eq,hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hout := mul_success_val x y out hmul
  rw [hxv,hyv] at hout
  exact hout

 theorem actual_raw_coefficients_of_input_bounds (self rhs : AspisR1CanonicalDotFinish.canonical.Q)
    (out : Array U64 4#usize)
    (hraw : AspisR1CanonicalDotFinish.canonical.Q.raw self rhs = .ok out)
    (hself0 : self.val[0]!.val ≤ 2^31-2) (hself1 : self.val[1]!.val ≤ 2^31-2)
    (hself2 : self.val[2]!.val ≤ 2^31-2) (hself3 : self.val[3]!.val ≤ 2^31-2)
    (hrhs0 : rhs.val[0]!.val ≤ 2^31-2) (hrhs1 : rhs.val[1]!.val ≤ 2^31-2)
    (hrhs2 : rhs.val[2]!.val ≤ 2^31-2) (hrhs3 : rhs.val[3]!.val ≤ 2^31-2)
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
  rcases hbody with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,
    h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  have hbodyRebuild : AspisR1CanonicalDotFinish.Proof.QRawTraceBody self rhs out
      v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h v_i v_i1 v_i2 v_i3 v_i4 v_u
      v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12 v_i13 v_i14 v_i15 v_i16
      v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24 v_i25 v_i26 v_i27 v_i28
      v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36 v_i37 v_i38 v_i39 :=
    ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,
      h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,
      h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  have hm0 := closure_zero_map_val_local self v_a h1
  have hm1 := closure_one_map_val_local rhs v_a2 h6
  have ba := map_index_eq_local self v_a 0#usize (by decide) hm0 v_a1 h2
  have bb := map_index_eq_local self v_a 1#usize (by decide) hm0 v_b h3
  have bc := map_index_eq_local self v_a 2#usize (by decide) hm0 v_c h4
  have bd := map_index_eq_local self v_a 3#usize (by decide) hm0 v_d h5
  have be := map_index_eq_local rhs v_a2 0#usize (by decide) hm1 v_e h7
  have bf := map_index_eq_local rhs v_a2 1#usize (by decide) hm1 v_f h8
  have bg := map_index_eq_local rhs v_a2 2#usize (by decide) hm1 v_g h9
  have bh := map_index_eq_local rhs v_a2 3#usize (by decide) hm1 v_h h10
  have hboundA : v_a1.val ≤ 2^31-2 := by rw [ba]; simpa using hself0
  have hboundB : v_b.val ≤ 2^31-2 := by rw [bb]; simpa using hself1
  have hboundC : v_c.val ≤ 2^31-2 := by rw [bc]; simpa using hself2
  have hboundD : v_d.val ≤ 2^31-2 := by rw [bd]; simpa using hself3
  have hboundE : v_e.val ≤ 2^31-2 := by rw [be]; simpa using hrhs0
  have hboundF : v_f.val ≤ 2^31-2 := by rw [bf]; simpa using hrhs1
  have hboundG : v_g.val ≤ 2^31-2 := by rw [bg]; simpa using hrhs2
  have hboundH : v_h.val ≤ 2^31-2 := by rw [bh]; simpa using hrhs3
  have hguard := AspisR1S5CurrentRepin.trace_no_wrap_of_canonical_limbs
    self rhs out v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h
    v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11
    v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23
    v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35
    v_i36 v_i37 v_i38 v_i39 hboundA hboundB hboundC hboundD hboundE hboundF hboundG hboundH hbodyRebuild
  rcases hguard with ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18⟩
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
    rw [← hcast]
    change (UScalar.cast .U64 AspisR1CanonicalDotFinish.canonical.P).val = P
    rw [UScalar.cast_val_eq]
    have hp : AspisR1CanonicalDotFinish.canonical.P.val = P := by
      norm_num [AspisR1CanonicalDotFinish.canonical.P, P, UScalar.ofNatCore_val_eq]
    rw [hp]
    exact Nat.mod_eq_of_lt (by norm_num [P])
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
    rw [hmulAe, hpp, hmulBf, hmulTwoU, hthreeP, hcastP, hrawU, hrawV] <;> omega
  have hc1 : v_i23.val = AspisR1.R22RawQmProductResidues.rawC1
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC1
    rw [w11,w10,w9,hmulAf,hmulBe,hmulTwoV,hrawU,hrawV] <;> omega
  have hc2 : v_i32.val = AspisR1.R22RawQmProductResidues.rawC2
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC2
    rw [w15,w14,w13,w12,hmulAg,hmulCe,hmulTwoPP,hpp,hmulBh,hmulDf]
    simp only [Nat.mul_assoc]
  have hc3 : v_i39.val = AspisR1.R22RawQmProductResidues.rawC3
      v_a1.val v_b.val v_c.val v_d.val v_e.val v_f.val v_g.val v_h.val := by
    unfold AspisR1.R22RawQmProductResidues.rawC3
    rw [w18,w17,w16,hmulAh,hmulBg,hmulCf,hmulDe] <;> omega
  have hout := h53
  exact ⟨v_a1.val, v_b.val, v_c.val, v_d.val, v_e.val, v_f.val, v_g.val,
    v_h.val, v_i17, v_i23, v_i32, v_i39, hout, hc0, hc1, hc2, hc3⟩
#print axioms actual_raw_coefficients_of_input_bounds
#print axioms AspisR1QRawValueBridge.qraw_success_uv
#print axioms AspisR1CanonicalDotFinish.canonical.Q.raw.PP
#print axioms AspisR1S5CurrentRepin.trace_no_wrap_of_canonical_limbs
end AspisR1QRawActualC0
