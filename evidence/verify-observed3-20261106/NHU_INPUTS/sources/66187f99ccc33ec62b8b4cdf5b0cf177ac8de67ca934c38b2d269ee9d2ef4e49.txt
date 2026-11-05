import NHU_U64Product
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1.NHU_InterpolationRaw
open NHU_U64Product

def raw (w0 w1 w2 c0 c1 c2 : U32) : Result U64 := do
 let p0←product w0 c0
 let p1←product w1 c1
 let s←p0+p1
 let p2←product w2 c2
 s+p2

theorem result (w0 w1 w2 c0 c1 c2 : U32)
 (hw0 : w0.val<2147483647) (hw1 : w1.val<2147483647) (hw2 : w2.val<2147483647)
 (hc0 : c0.val<2147483647) (hc1 : c1.val<2147483647) (hc2 : c2.val<2147483647) :
 ∃ out,raw w0 w1 w2 c0 c1 c2=ok out ∧
 out.val=w0.val*c0.val+w1.val*c1.val+w2.val*c2.val ∧ out.val≤3*P2 := by
 obtain ⟨p0,h0,v0,b0⟩:=NHU_U64Product.result w0 c0 hw0 hc0
 obtain ⟨p1,h1,v1,b1⟩:=NHU_U64Product.result w1 c1 hw1 hc1
 obtain ⟨p2,h2,v2,b2⟩:=NHU_U64Product.result w2 c2 hw2 hc2
 have spec1 : (p0+p1 : Result U64) ⦃ out=>out.val=p0.val+p1.val ⦄ := by
  apply UScalar.add_spec
  scalar_tac
 obtain ⟨sum,call,value⟩:=WP.spec_imp_exists spec1
 have spec2 : (sum+p2 : Result U64) ⦃ out=>out.val=sum.val+p2.val ⦄ := by
  apply UScalar.add_spec
  scalar_tac
 obtain ⟨out,call2,value2⟩:=WP.spec_imp_exists spec2
 refine ⟨out,?_,?_,?_⟩
 · simp only [raw,h0,h1,h2,call,call2,bind_tc_ok]
 · omega
 · omega
#print axioms result
end AspisR1.NHU_InterpolationRaw
