import NGW_RefLinear
import NGW_ProductLaw
import NGM_DoubleModel
set_option autoImplicit false
namespace NGW_PointValue
open Aeneas Aeneas.Std Result NGW_ConstructorQM
abbrev words := NGM_DoubleModel.words

def arithmetic (bit carry product : Q) : Result Q := do
 let sum ← FIn_WeightsExtract.field.QM31.add bit carry
 let twice ← FIn_WeightsExtract.field.QM31.add product product
 FIn_WeightsExtract.field.QM31.sub sum twice

theorem observed (bit carry product : Q) (hb : Canon bit) (hc : Canon carry) (hp : Canon product) :
 NGW_HelperRef.point_ref (words bit) (words carry) (words product) =
 (do let value ← arithmetic bit carry product;ok (words value)) := by
 rcases hb with ⟨⟨hb0,hb1⟩,⟨hb2,hb3⟩⟩
 rcases hc with ⟨⟨hc0,hc1⟩,⟨hc2,hc3⟩⟩
 rcases hp with ⟨⟨hp0,hp1⟩,⟨hp2,hp3⟩⟩
 obtain ⟨s0,t0,v0,hs0,ht0,hv0,cs0,ct0,_⟩ := NGW_RefLinear.cell bit.c0.a carry.c0.a product.c0.a hb0 hc0 hp0
 obtain ⟨s1,t1,v1,hs1,ht1,hv1,cs1,ct1,_⟩ := NGW_RefLinear.cell bit.c0.b carry.c0.b product.c0.b hb1 hc1 hp1
 obtain ⟨s2,t2,v2,hs2,ht2,hv2,cs2,ct2,_⟩ := NGW_RefLinear.cell bit.c1.a carry.c1.a product.c1.a hb2 hc2 hp2
 obtain ⟨s3,t3,v3,hs3,ht3,hv3,cs3,ct3,_⟩ := NGW_RefLinear.cell bit.c1.b carry.c1.b product.c1.b hb3 hc3 hp3
 have sub0 := NGW_RefLinear.sub s0 t0 cs0 ct0
 have sub1 := NGW_RefLinear.sub s1 t1 cs1 ct1
 have sub2 := NGW_RefLinear.sub s2 t2 cs2 ct2
 have sub3 := NGW_RefLinear.sub s3 t3 cs3 ct3
 simp [NGW_HelperRef.point_ref,words,NGM_DoubleModel.words,Array.make,Array.index_usize,NGW_RefLinear.add,arithmetic,FIn_WeightsExtract.field.QM31.add,FIn_WeightsExtract.field.CM31.add,FIn_WeightsExtract.field.QM31.sub,FIn_WeightsExtract.field.CM31.sub,hs0,hs1,hs2,hs3,ht0,ht1,ht2,ht3,hv0,hv1,hv2,hv3,sub0,sub1,sub2,sub3]

#print axioms observed
end NGW_PointValue
