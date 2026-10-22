import QRawPPPositiveTotalityV1
import QRawU64LimbProductTotalityV1
import QRawCheckedMultiplyTotalityV1
import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5QRawCheckedProducts

abbrev U64 := UScalar UScalarTy.U64

private theorem total_mul (x y : U64) (h : x.val * y.val ≤ UScalar.max UScalarTy.U64) :
    ∃ z : U64, UScalar.mul x y = .ok z := by
  obtain ⟨z,hz,_⟩ := AspisR1S5QRawTotality.u64_mul_total_of_le x y h
  exact ⟨z,hz⟩

/-- The exact 20 checked multiplications in the emitted raw routine all have
successful results. The eight field-limb products use the exact map/index
coordinates; the four scale products use their source range bounds. -/
theorem all_checked_products_total
    (a b c d e f g h : U64)
    (u v : U64) (hu : u.val < 10737418240) (hv : v.val < 10737418240)
    (ha : a.val ≤ 2^31-2) (hb : b.val ≤ 2^31-2)
    (hc : c.val ≤ 2^31-2) (hd : d.val ≤ 2^31-2)
    (he : e.val ≤ 2^31-2) (hf : f.val ≤ 2^31-2)
    (hg : g.val ≤ 2^31-2) (hh : h.val ≤ 2^31-2) :
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
        (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P) = .ok threeP ∧
      a.val ≤ 2^31-2 ∧ b.val ≤ 2^31-2 ∧ c.val ≤ 2^31-2 ∧ d.val ≤ 2^31-2 ∧
      e.val ≤ 2^31-2 ∧ f.val ≤ 2^31-2 ∧ g.val ≤ 2^31-2 ∧ h.val ≤ 2^31-2 := by
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
  obtain ⟨cg,hcg,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c g hc hg
  obtain ⟨dh,hdh,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d h hd hh
  obtain ⟨ch,hch,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c h hc hh
  obtain ⟨dg,hdg,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d g hd hg
  obtain ⟨ae,hae,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total a e ha he
  obtain ⟨bf,hbf,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total b f hb hf
  obtain ⟨af,haf,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total a f ha hf
  obtain ⟨be,hbe,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total b e hb he
  obtain ⟨ag,hag,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total a g ha hg
  obtain ⟨ce,hce,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c e hc he
  obtain ⟨bh,hbh,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total b h hb hh
  obtain ⟨df,hdf,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d f hd hf
  obtain ⟨ah,hah,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total a h ha hh
  obtain ⟨bg,hbg,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total b g hb hg
  obtain ⟨cf,hcf,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total c f hc hf
  obtain ⟨de,hde,_⟩ := AspisR1S5QRawCanonicalProductTotality.u64_canonical_limb_product_total d e hd he
  exact ⟨pp,twoU,twoV,twoPP,threeP,
    ⟨cg,dh,ch,dg,ae,bf,af,be,ag,ce,bh,df,ah,bg,cf,de,
      hcg,hdh,hch,hdg,hae,hbf,haf,hbe,hag,hce,hbh,hdf,hah,hbg,hcf,hde⟩,
    htwoU,htwoV,hpp,htwoPP,hthreeP,
    ha,hb,hc,hd,he,hf,hg,hh⟩

#print axioms all_checked_products_total
end AspisR1S5QRawCheckedProducts
