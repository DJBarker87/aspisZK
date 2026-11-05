import NGW_ProductLaw
import NGW_ConstructorArrays
set_option autoImplicit false
namespace NGW_FactorRow
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays

def source (a b : Q) : Result (Array Q 4#usize) := do
 let aa ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE a
 let bb ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE b
 let p0 ← FIn_WeightsExtract.field.QM31.mul aa bb
 let p1 ← FIn_WeightsExtract.field.QM31.mul a bb
 let p2 ← FIn_WeightsExtract.field.QM31.mul aa b
 let p3 ← FIn_WeightsExtract.field.QM31.mul a b
 ok (Array.make 4#usize [p0,p1,p2,p3])

theorem total (a b : Q) (ha : Canon a) (hb : Canon b) :
 ∃ aa bb p0 p1 p2 p3,
 FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE a=ok aa ∧ Canon aa ∧
 FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE b=ok bb ∧ Canon bb ∧
 FIn_WeightsExtract.field.QM31.mul aa bb=ok p0 ∧
 FIn_WeightsExtract.field.QM31.mul a bb=ok p1 ∧
 FIn_WeightsExtract.field.QM31.mul aa b=ok p2 ∧
 FIn_WeightsExtract.field.QM31.mul a b=ok p3 ∧
 source a b=ok (Array.make 4#usize [p0,p1,p2,p3]) ∧
 Holds Canon (Array.make 4#usize [p0,p1,p2,p3]) := by
 obtain ⟨aa,haa,caa⟩ := sub FIn_WeightsExtract.field.QM31.ONE a one ha
 obtain ⟨bb,hbb,cbb⟩ := sub FIn_WeightsExtract.field.QM31.ONE b one hb
 obtain ⟨p0,h0,c0,_⟩ := NGW_ProductLaw.total aa bb caa cbb
 obtain ⟨p1,h1,c1,_⟩ := NGW_ProductLaw.total a bb ha cbb
 obtain ⟨p2,h2,c2,_⟩ := NGW_ProductLaw.total aa b caa hb
 obtain ⟨p3,h3,c3,_⟩ := NGW_ProductLaw.total a b ha hb
 refine ⟨aa,bb,p0,p1,p2,p3,haa,caa,hbb,cbb,h0,h1,h2,h3,?_,?_⟩
 · simp only [source,haa,hbb,h0,h1,h2,h3,bind_tc_ok]
 · intro q hq
   simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl
   · exact c0
   · exact c1
   · exact c2
   · exact c3

#print axioms total
end NGW_FactorRow
