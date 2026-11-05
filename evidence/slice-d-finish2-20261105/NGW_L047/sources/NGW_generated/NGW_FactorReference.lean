import NGW_FactorRef.Funs
import NGW_RefLinear
import NGW_ConstructorQM
import NGM_DoubleModel
set_option autoImplicit false
namespace NGW_FactorReference
open Aeneas Aeneas.Std Result NGW_ConstructorQM
abbrev words := NGM_DoubleModel.words

theorem sub_alias (x y : U32) : NGW_FactorRef.sub_ref x y=NGW_HelperRef.sub_ref x y := rfl

theorem one_sub (a : Q) (ha : Canon a) :
 NGW_FactorRef.one_sub (words a)=
 (do let aa ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE a;ok (words aa)) := by
 rcases ha with ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
 have e0 := NGW_RefLinear.sub 1#u32 a.c0.a (by decide) h0
 have e1 := NGW_RefLinear.sub 0#u32 a.c0.b (by decide) h1
 have e2 := NGW_RefLinear.sub 0#u32 a.c1.a (by decide) h2
 have e3 := NGW_RefLinear.sub 0#u32 a.c1.b (by decide) h3
 obtain ⟨v0,hv0,_⟩ := NGW_RefLinear.sub_total 1#u32 a.c0.a (by decide) h0
 obtain ⟨v1,hv1,_⟩ := NGW_RefLinear.sub_total 0#u32 a.c0.b (by decide) h1
 obtain ⟨v2,hv2,_⟩ := NGW_RefLinear.sub_total 0#u32 a.c1.a (by decide) h2
 obtain ⟨v3,hv3,_⟩ := NGW_RefLinear.sub_total 0#u32 a.c1.b (by decide) h3
 simp [NGW_FactorRef.one_sub,words,NGM_DoubleModel.words,Array.make,Array.index_usize,sub_alias,e0,e1,e2,e3,
   FIn_WeightsExtract.field.QM31.sub,FIn_WeightsExtract.field.CM31.sub,FIn_WeightsExtract.field.QM31.ONE,hv0,hv1,hv2,hv3]

theorem factor (a b : Q) (ha : Canon a) (hb : Canon b)
 (replies : Array (Array U32 4#usize) 4#usize) :
 ∃ aa bb,FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE a=ok aa ∧
 FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE b=ok bb ∧
 NGW_FactorRef.factor_ref (words a) (words b) replies=ok
   ⟨Array.make 4#usize [words aa,words a,words aa,words a],
    Array.make 4#usize [words bb,words bb,words b,words b],replies⟩ := by
 obtain ⟨aa,haa,_⟩ := sub FIn_WeightsExtract.field.QM31.ONE a one ha
 obtain ⟨bb,hbb,_⟩ := sub FIn_WeightsExtract.field.QM31.ONE b one hb
 have ra := one_sub a ha
 have rb := one_sub b hb
 rw [haa] at ra
 rw [hbb] at rb
 simp only [bind_tc_ok] at ra rb
 exact ⟨aa,bb,haa,hbb,by simp only [NGW_FactorRef.factor_ref,ra,rb,bind_tc_ok]⟩

#print axioms sub_alias
#print axioms one_sub
#print axioms factor
end NGW_FactorReference
