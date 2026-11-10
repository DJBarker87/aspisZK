import NPH_R22QRawShift
import JGi_QRawSourceForwardTotalityV1

/-! NPH_ (R22, Q.raw item, 2026-11-10 continuation): both canonical.Q.raw copies are TOTAL (a).
The body's only overflow-checked operations are
- the sixteen limb products `x * y` of u32 limbs widened to u64: each is at most
  (2^32-1)^2 < 2^64, so they succeed for EVERY limb value (no canonicality needed);
- PP = P*P, 2*u and 2*v (u, v are closure_2 outputs, < 10737418240), 2*PP and 3*P;
- the checked shift `x >>> 31` inside closure_2 (succeeds for every x).
Every addition and subtraction is an explicit wrapping_* call. So the checked body returns ok
for every pair of inputs. The proof is the closure proof
AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs with the limb hypotheses
`≤ 2^31-2` replaced by the u32 type bound `< 2^32`; the trace-body assembly
(success_of_trace_body) is reused unchanged.
- `prod32`: a u64 product of two values below 2^32 succeeds.
- `products32`: the twenty checked multiplications succeed for limbs below 2^32.
- `unified_total`: AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs is ok for every input.
- `fio_total`: FIo_QRaw.canonical.Q.raw is ok for every input (definitional copy, qraw_eq).
This replaces the caller joins of section 19e (canonical g at op20, the FIo weights pushes,
the claim-dot pushes): a TOTAL definition needs no caller tie. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22QRawTotal
open Aeneas Aeneas.Std Result

abbrev U64 := UScalar UScalarTy.U64

theorem u32_lt (x : U32) : x.val < 2^32 := by
  first
  | scalar_tac
  | exact x.hBounds
  | (have h := x.bv.isLt; simpa using h)

theorem prod32 (x y : U64) (hx : x.val < 2^32) (hy : y.val < 2^32) :
    ∃ z : U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val := by
  have hx' : x.val ≤ 2^32 - 1 := by omega
  have hy' : y.val ≤ 2^32 - 1 := by omega
  have hprod : x.val * y.val ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul hx' hy'
  have hmax : x.val * y.val ≤ UScalar.max UScalarTy.U64 := by
    calc
      x.val * y.val ≤ (2^32 - 1) * (2^32 - 1) := hprod
      _ ≤ 2^64 - 1 := by norm_num
      _ = UScalar.max UScalarTy.U64 := by
        rw [UScalar.max, UScalarTy.U64_numBits_eq]
  exact AspisR1S5QRawTotality.u64_mul_total_of_le x y hmax

private theorem total_mul (x y : U64) (h : x.val * y.val ≤ UScalar.max UScalarTy.U64) :
    ∃ z : U64, UScalar.mul x y = .ok z := by
  obtain ⟨z,hz,_⟩ := AspisR1S5QRawTotality.u64_mul_total_of_le x y h
  exact ⟨z,hz⟩

theorem products32
    (a b c d e f g h : U64)
    (u v : U64) (hu : u.val < 10737418240) (hv : v.val < 10737418240)
    (ha : a.val < 2^32) (hb : b.val < 2^32)
    (hc : c.val < 2^32) (hd : d.val < 2^32)
    (he : e.val < 2^32) (hf : f.val < 2^32)
    (hg : g.val < 2^32) (hh : h.val < 2^32) :
    ∃ pp twoU twoV twoPP threeP : U64,
      (∃ cg dh ch dg ae bf af be ag ce bh df ah bg cf de : U64,
        UScalar.mul c g = .ok cg ∧ UScalar.mul d h = .ok dh ∧
        UScalar.mul c h = .ok ch ∧ UScalar.mul d g = .ok dg ∧
        UScalar.mul a e = .ok ae ∧ UScalar.mul b f = .ok bf ∧
        UScalar.mul a f = .ok af ∧ UScalar.mul b e = .ok be ∧
        UScalar.mul a g = .ok ag ∧ UScalar.mul c e = .ok ce ∧
        UScalar.mul b h = .ok bh ∧ UScalar.mul d f = .ok df ∧
        UScalar.mul a h = .ok ah ∧ UScalar.mul b g = .ok bg ∧
        UScalar.mul c f = .ok cf ∧ UScalar.mul d e = .ok de) ∧
      UScalar.mul (2#u64) u = .ok twoU ∧
      UScalar.mul (2#u64) v = .ok twoV ∧
      AspisR1CanonicalQRawUnified.canonical.Q.raw.PP = .ok pp ∧
      UScalar.mul (2#u64) pp = .ok twoPP ∧
      UScalar.mul (3#u64)
        (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P) = .ok threeP := by
  have htwoVal : (2#u64).val = 2 := by norm_num [UScalar.ofNatCore_val_eq]
  have hmaxU : (2#u64).val * u.val ≤ UScalar.max UScalarTy.U64 := by
    rw [htwoVal, UScalar.max, UScalarTy.U64_numBits_eq]
    omega
  have hmaxV : (2#u64).val * v.val ≤ UScalar.max UScalarTy.U64 := by
    rw [htwoVal, UScalar.max, UScalarTy.U64_numBits_eq]
    omega
  obtain ⟨twoU,htwoU⟩ := total_mul (2#u64) u hmaxU
  obtain ⟨twoV,htwoV⟩ := total_mul (2#u64) v hmaxV
  obtain ⟨pp,hpp,hppBound⟩ := AspisR1S5QRawTotality.pp_total
  have hmaxPP : (2#u64).val * pp.val ≤ UScalar.max UScalarTy.U64 := by
    rw [htwoVal, hppBound, UScalar.max, UScalarTy.U64_numBits_eq]
    norm_num
  obtain ⟨twoPP,htwoPP⟩ := total_mul (2#u64) pp hmaxPP
  have hp : AspisR1CanonicalQRawUnified.canonical.P.val = 2147483647 := by
    norm_num [AspisR1CanonicalQRawUnified.canonical.P, UScalar.ofNatCore_val_eq]
  have hpCast :
      (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P).val = 2147483647 := by
    change (UScalar.cast .U64 AspisR1CanonicalQRawUnified.canonical.P).val = _
    rw [UScalar.cast_val_eq, hp]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hthreeVal : (3#u64).val = 3 := by norm_num [UScalar.ofNatCore_val_eq]
  have hmaxThree : (3#u64).val *
      (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P).val ≤
      UScalar.max UScalarTy.U64 := by
    rw [hthreeVal,hpCast,UScalar.max,UScalarTy.U64_numBits_eq]
    norm_num
  obtain ⟨threeP,hthreeP⟩ := total_mul (3#u64)
    (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P) hmaxThree
  obtain ⟨cg,hcg,_⟩ := prod32 c g hc hg
  obtain ⟨dh,hdh,_⟩ := prod32 d h hd hh
  obtain ⟨ch,hch,_⟩ := prod32 c h hc hh
  obtain ⟨dg,hdg,_⟩ := prod32 d g hd hg
  obtain ⟨ae,hae,_⟩ := prod32 a e ha he
  obtain ⟨bf,hbf,_⟩ := prod32 b f hb hf
  obtain ⟨af,haf,_⟩ := prod32 a f ha hf
  obtain ⟨be,hbe,_⟩ := prod32 b e hb he
  obtain ⟨ag,hag,_⟩ := prod32 a g ha hg
  obtain ⟨ce,hce,_⟩ := prod32 c e hc he
  obtain ⟨bh,hbh,_⟩ := prod32 b h hb hh
  obtain ⟨df,hdf,_⟩ := prod32 d f hd hf
  obtain ⟨ah,hah,_⟩ := prod32 a h ha hh
  obtain ⟨bg,hbg,_⟩ := prod32 b g hb hg
  obtain ⟨cf,hcf,_⟩ := prod32 c f hc hf
  obtain ⟨de,hde,_⟩ := prod32 d e hd he
  exact ⟨pp,twoU,twoV,twoPP,threeP,
    ⟨cg,dh,ch,dg,ae,bf,af,be,ag,ce,bh,df,ah,bg,cf,de,
      hcg,hdh,hch,hdg,hae,hbf,haf,hbe,hag,hce,hbh,hdf,hah,hbg,hcf,hde⟩,
    htwoU,htwoV,hpp,htwoPP,hthreeP⟩

/-- The Unified canonical.Q.raw is ok for EVERY pair of inputs. -/
theorem unified_total (self rhs : AspisR1CanonicalQRawUnified.canonical.Q) :
    ∃ out : Array Std.U64 4#usize,
      AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs = .ok out := by
  rcases AspisR1CanonicalQRawUnified.Proof.qraw_input_prefix_total self rhs with
    ⟨mappedL,mappedR,hmapL,hmapR,⟨a,b,c,d,haRead,hbRead,hcRead,hdRead⟩,
      ⟨e,f,g,h,heRead,hfRead,hgRead,hhRead⟩⟩
  have hmL := AspisR1QRawActualC0V2.closure_zero_map_val_local self mappedL hmapL
  have hmR := AspisR1QRawActualC0V2.closure_one_map_val_local rhs mappedR hmapR
  have hia : a.val = self.val[0]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local self mappedL 0#usize
      (by decide) hmL a haRead
  have hib : b.val = self.val[1]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local self mappedL 1#usize
      (by decide) hmL b hbRead
  have hic : c.val = self.val[2]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local self mappedL 2#usize
      (by decide) hmL c hcRead
  have hid : d.val = self.val[3]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local self mappedL 3#usize
      (by decide) hmL d hdRead
  have hie : e.val = rhs.val[0]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local rhs mappedR 0#usize
      (by decide) hmR e heRead
  have hif : f.val = rhs.val[1]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local rhs mappedR 1#usize
      (by decide) hmR f hfRead
  have hig : g.val = rhs.val[2]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local rhs mappedR 2#usize
      (by decide) hmR g hgRead
  have hih : h.val = rhs.val[3]!.val := by
    simpa using AspisR1QRawActualC0V2.map_index_eq_local rhs mappedR 3#usize
      (by decide) hmR h hhRead
  have hab : a.val < 2^32 := by rw [hia]; exact u32_lt _
  have hbb : b.val < 2^32 := by rw [hib]; exact u32_lt _
  have hcb : c.val < 2^32 := by rw [hic]; exact u32_lt _
  have hdb : d.val < 2^32 := by rw [hid]; exact u32_lt _
  have heb : e.val < 2^32 := by rw [hie]; exact u32_lt _
  have hfb : f.val < 2^32 := by rw [hif]; exact u32_lt _
  have hgb : g.val < 2^32 := by rw [hig]; exact u32_lt _
  have hhb : h.val < 2^32 := by rw [hih]; exact u32_lt _
  obtain ⟨cg,hcg,_⟩ := prod32 c g hcb hgb
  obtain ⟨dh,hdh,_⟩ := prod32 d h hdb hhb
  obtain ⟨ch,hch,_⟩ := prod32 c h hcb hhb
  obtain ⟨dg,hdg,_⟩ := prod32 d g hdb hgb
  obtain ⟨pp,hpp,_⟩ := AspisR1S5QRawTotality.pp_total
  let i2 : U64 := U64.wrapping_add cg pp
  let i4 : U64 := U64.wrapping_sub i2 dh
  let i7 : U64 := U64.wrapping_add ch dg
  let i1 : U64 := pp
  have hi2 : lift (core.num.U64.wrapping_add cg pp) = .ok i2 := rfl
  have hi4 : lift (core.num.U64.wrapping_sub i2 dh) = .ok i4 := rfl
  have hi7 : lift (core.num.U64.wrapping_add ch dg) = .ok i7 := rfl
  obtain ⟨u,hu,hufold⟩ := AspisR1CanonicalQRawUnified.Proof.qRawPartial_success i4
  obtain ⟨v,hv,hvfold⟩ := AspisR1CanonicalQRawUnified.Proof.qRawPartial_success i7
  have huBound : u.val < 10737418240 := by
    rw [hufold]
    exact AspisV8R17.RawReducer.first_fold_lt i4.val i4.bv.isLt
  have hvBound : v.val < 10737418240 := by
    rw [hvfold]
    exact AspisV8R17.RawReducer.first_fold_lt i7.val i7.bv.isLt
  obtain ⟨pp',twoU,twoV,twoPP,threeP,hproducts,htwoU,htwoV,hpp',htwoPP,hthreeP⟩ :=
      products32 a b c d e f g h u v huBound hvBound hab hbb hcb hdb heb hfb hgb hhb
  have hppEq : pp' = pp := Result.ok.inj (hpp'.symm.trans hpp)
  subst pp'
  rcases hproducts with ⟨i,i3,i5,i6,i8,i10,i18,i19,i24,i25,i29,i31,i33,i34,i36,i38,
    h11,h14,h17,h18,h21,h23,h31,h32,h37,h38,h42,h44,h46,h47,h49,h51⟩
  have hcgEq : cg = i := Result.ok.inj (hcg.symm.trans h11)
  have hdhEq : dh = i3 := Result.ok.inj (hdh.symm.trans h14)
  have hchEq : ch = i5 := Result.ok.inj (hch.symm.trans h17)
  have hdgEq : dg = i6 := Result.ok.inj (hdg.symm.trans h18)
  have hi2' := hi2
  rw [hcgEq] at hi2'
  have hi4' := hi4
  rw [hdhEq] at hi4'
  have hi7' := hi7
  rw [hchEq, hdgEq] at hi7'
  let i12 : U64 := twoU
  let i15 : U64 := threeP
  let i22 : U64 := twoV
  let i27 : U64 := twoPP
  let i9 : U64 := U64.wrapping_add i8 pp
  let i11 : U64 := U64.wrapping_sub i9 i10
  let i13 : U64 := U64.wrapping_add i11 twoU
  let i14 : U64 := core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P
  let i16 : U64 := U64.wrapping_add i13 threeP
  let i17 : U64 := U64.wrapping_sub i16 v
  let i20 : U64 := U64.wrapping_add i18 i19
  let i21 : U64 := U64.wrapping_add i20 u
  let i23 : U64 := U64.wrapping_add i21 twoV
  let i26 : U64 := U64.wrapping_add i24 i25
  let i28 : U64 := U64.wrapping_add i26 twoPP
  let i30 : U64 := U64.wrapping_sub i28 i29
  let i32 : U64 := U64.wrapping_sub i30 i31
  let i35 : U64 := U64.wrapping_add i33 i34
  let i37 : U64 := U64.wrapping_add i35 i36
  let i39 : U64 := U64.wrapping_add i37 i38
  let out : Array Std.U64 4#usize := Array.make 4#usize [i17,i23,i32,i39]
  have h13 : lift (core.num.U64.wrapping_add i i1) = .ok i2 := hi2'
  have h15 : lift (core.num.U64.wrapping_sub i2 i3) = .ok i4 := hi4'
  have h19 : lift (core.num.U64.wrapping_add i5 i6) = .ok i7 := hi7'
  have h22 : lift (core.num.U64.wrapping_add i8 i1) = .ok i9 := rfl
  have h24 : lift (core.num.U64.wrapping_sub i9 i10) = .ok i11 := rfl
  have h26 : lift (core.num.U64.wrapping_add i11 i12) = .ok i13 := rfl
  have h27 : lift (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P) = .ok i14 := rfl
  have h29 : lift (core.num.U64.wrapping_add i13 i15) = .ok i16 := rfl
  have h30 : lift (core.num.U64.wrapping_sub i16 v) = .ok i17 := rfl
  have h33 : lift (core.num.U64.wrapping_add i18 i19) = .ok i20 := rfl
  have h34 : lift (core.num.U64.wrapping_add i20 u) = .ok i21 := rfl
  have h36 : lift (core.num.U64.wrapping_add i21 i22) = .ok i23 := rfl
  have h39 : lift (core.num.U64.wrapping_add i24 i25) = .ok i26 := rfl
  have h41 : lift (core.num.U64.wrapping_add i26 i27) = .ok i28 := rfl
  have h43 : lift (core.num.U64.wrapping_sub i28 i29) = .ok i30 := rfl
  have h45 : lift (core.num.U64.wrapping_sub i30 i31) = .ok i32 := rfl
  have h48 : lift (core.num.U64.wrapping_add i33 i34) = .ok i35 := rfl
  have h50 : lift (core.num.U64.wrapping_add i35 i36) = .ok i37 := rfl
  have h52 : lift (core.num.U64.wrapping_add i37 i38) = .ok i39 := rfl
  have h53 : out = Array.make 4#usize [i17,i23,i32,i39] := rfl
  have hbody : AspisR1CanonicalQRawUnified.Proof.QRawTraceBody self rhs out
      mappedL a b c d mappedR e f g h i pp i2 i3 i4 u i5 i6 i7 v i8 i9 i10 i11
      twoU i13 i14 threeP i16 i17 i18 i19 i20 i21 twoV i23 i24 i25 i26 twoPP i28
      i29 i30 i31 i32 i33 i34 i35 i36 i37 i38 i39 := by
    exact ⟨hmapL,haRead,hbRead,hcRead,hdRead,hmapR,heRead,hfRead,hgRead,hhRead,
      h11,hpp,h13,h14,h15,hu,h17,h18,h19,hv,h21,h22,h23,h24,htwoU,h26,h27,
      hthreeP,h29,h30,h31,h32,h33,h34,htwoV,h36,h37,h38,h39,htwoPP,h41,h42,
      h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  exact ⟨out, AspisR1S5QRawSourceTotality.success_of_trace_body self rhs out
    mappedL a b c d mappedR e f g h i pp i2 i3 i4 u i5 i6 i7 v i8 i9 i10 i11
    twoU i13 i14 threeP i16 i17 i18 i19 i20 i21 twoV i23 i24 i25 i26 twoPP i28
    i29 i30 i31 i32 i33 i34 i35 i36 i37 i38 i39 hbody⟩

/-- The FIo copy (definitionally the Unified body, NPH_R22QRawShift.qraw_eq) is ok for EVERY
pair of inputs. -/
theorem fio_total (self rhs : FIo_QRaw.canonical.Q) :
    ∃ out : Array Std.U64 4#usize, FIo_QRaw.canonical.Q.raw self rhs = .ok out := by
  rw [AspisR1.NPH_R22QRawShift.qraw_eq]
  exact unified_total self rhs

#print axioms u32_lt
#print axioms prod32
#print axioms products32
#print axioms unified_total
#print axioms fio_total
end AspisR1.NPH_R22QRawTotal
