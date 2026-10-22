import QRawInputPrefixTotalityV1
import S5QRaw.NoWrapFactsV5
import QRawInputCoordinateBoundsV1
import QRawCheckedProductsTotalityV1
import S5QRaw.ActualCoefficientsFromBoundsV2
import QRawSuccessOfTraceBodyV1
import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5QRawSourceTotality

open AspisR1CanonicalQRawUnified

abbrev U64 := UScalar UScalarTy.U64

/-- The exact emitted Q.raw source function is successful whenever all eight
input limbs are canonical. Its checked products are derived from canonical
coordinate bounds and the two actual closure outputs; all wrap operations are
total and require no no-wrap assumption for success. -/
theorem qraw_total_of_canonical_limbs
    (self rhs : AspisR1CanonicalQRawUnified.canonical.Q)
    (hself0 : self.val[0]!.val ≤ 2^31-2) (hself1 : self.val[1]!.val ≤ 2^31-2)
    (hself2 : self.val[2]!.val ≤ 2^31-2) (hself3 : self.val[3]!.val ≤ 2^31-2)
    (hrhs0 : rhs.val[0]!.val ≤ 2^31-2) (hrhs1 : rhs.val[1]!.val ≤ 2^31-2)
    (hrhs2 : rhs.val[2]!.val ≤ 2^31-2) (hrhs3 : rhs.val[3]!.val ≤ 2^31-2) :
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
  have hab : a.val ≤ 2^31-2 := by rw [hia]; exact hself0
  have hbb : b.val ≤ 2^31-2 := by rw [hib]; exact hself1
  have hcb : c.val ≤ 2^31-2 := by rw [hic]; exact hself2
  have hdb : d.val ≤ 2^31-2 := by rw [hid]; exact hself3
  have heb : e.val ≤ 2^31-2 := by rw [hie]; exact hrhs0
  have hfb : f.val ≤ 2^31-2 := by rw [hif]; exact hrhs1
  have hgb : g.val ≤ 2^31-2 := by rw [hig]; exact hrhs2
  have hhb : h.val ≤ 2^31-2 := by rw [hih]; exact hrhs3
  obtain ⟨cg,hcg,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c g hcb hgb
  obtain ⟨dh,hdh,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d h hdb hhb
  obtain ⟨ch,hch,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c h hcb hhb
  obtain ⟨dg,hdg,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d g hdb hgb
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
  obtain ⟨pp',twoU,twoV,twoPP,threeP,hproducts,htwoU,htwoV,hpp',htwoPP,hthreeP,
    hab',hbb',hcb',hdb',heb',hfb',hgb',hhb'⟩ :=
      AspisR1S5QRawCheckedProducts.all_checked_products_total
        a b c d e f g h u v huBound hvBound hab hbb hcb hdb heb hfb hgb hhb
  -- Determinism identifies the auxiliary `PP` result with the already-used
  -- first-bind witness. The product witnesses are then unpacked in source order.
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

#print axioms qraw_total_of_canonical_limbs
end AspisR1S5QRawSourceTotality
