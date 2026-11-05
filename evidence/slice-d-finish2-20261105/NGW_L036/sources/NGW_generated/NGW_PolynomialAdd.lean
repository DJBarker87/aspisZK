import NGW_RefLinear
import NGM_RawWords
import NGM_LPi_TowerValues
set_option autoImplicit false
namespace NGW_PolynomialAdd
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev words := AspisR1.NGM_RawWords.nativeWords

theorem total (x y : NE) (hx : canonE x) (hy : canonE y) :
 ∃ z,FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧ canonE z := by
 obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
 obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
 exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok],⟨ca,cb⟩⟩

theorem observed (product coefficient : NE) (hp : canonE product) (hc : canonE coefficient) :
 NGW_HelperRef.polynomial_step_ref (words product) (words coefficient)=
 (do let value ← FIo_Native.aspis_core.field.wide_exact.WideExact.add product coefficient;ok (words value)) := by
 rcases hp with ⟨⟨⟨hp0,hp1⟩,⟨hp2,hp3⟩⟩,⟨⟨hp4,hp5⟩,⟨hp6,hp7⟩⟩⟩
 rcases hc with ⟨⟨⟨hc0,hc1⟩,⟨hc2,hc3⟩⟩,⟨⟨hc4,hc5⟩,⟨hc6,hc7⟩⟩⟩
 obtain ⟨v0,hv0,_,_⟩ := LPi_NatBase.add product.c0.c0.a coefficient.c0.c0.a hp0 hc0
 obtain ⟨v1,hv1,_,_⟩ := LPi_NatBase.add product.c0.c0.b coefficient.c0.c0.b hp1 hc1
 obtain ⟨v2,hv2,_,_⟩ := LPi_NatBase.add product.c0.c1.a coefficient.c0.c1.a hp2 hc2
 obtain ⟨v3,hv3,_,_⟩ := LPi_NatBase.add product.c0.c1.b coefficient.c0.c1.b hp3 hc3
 obtain ⟨v4,hv4,_,_⟩ := LPi_NatBase.add product.c1.c0.a coefficient.c1.c0.a hp4 hc4
 obtain ⟨v5,hv5,_,_⟩ := LPi_NatBase.add product.c1.c0.b coefficient.c1.c0.b hp5 hc5
 obtain ⟨v6,hv6,_,_⟩ := LPi_NatBase.add product.c1.c1.a coefficient.c1.c1.a hp6 hc6
 obtain ⟨v7,hv7,_,_⟩ := LPi_NatBase.add product.c1.c1.b coefficient.c1.c1.b hp7 hc7
 simp [NGW_HelperRef.polynomial_step_ref,words,AspisR1.NGM_RawWords.nativeWords,Array.make,Array.index_usize,NGW_RefLinear.add,NGM_ProbeTransport.base_add,FIo_Native.aspis_core.field.wide_exact.WideExact.add,FIo_Native.aspis_core.field.QM31.add,FIo_Native.aspis_core.field.CM31.add,hv0,hv1,hv2,hv3,hv4,hv5,hv6,hv7]

#print axioms total
#print axioms observed
end NGW_PolynomialAdd
